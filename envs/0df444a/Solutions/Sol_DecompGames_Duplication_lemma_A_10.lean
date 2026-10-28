-- Prove2me | solution 1 for DecompGames.Duplication.lemma_A_10
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-28T15:15:36.783649+00:00
-- url     : https://prove2.me/submissions/d21635c3-1836-42a1-b84f-82e1f00d9a1b

import Mathlib
import Definitions.Def_DecompGames_Duplication_Operators
open Finset
namespace Queelius.GameProjection
open DecompGames.Duplication
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
  [∀ i,Fintype (S i)] [∀ i,DecidableEq (S i)]
lemma update_comparable (i : ι) (s t : ∀ i,S i) (hc : IsComparable i s t) :
    Function.update s i (t i)=t := by
  funext j
  by_cases hji : j=i
  · subst j
    simp
  · simp only [Function.update_of_ne hji]
    exact hc.2 j hji
lemma lam_update (μ : ∀ i,S i → ℝ) (i : ι) (h : (∀ j,S j) → ℝ) (s : ∀ j,S j) (a : S i) :
    lam μ i h (Function.update s i a)=lam μ i h s := by
  simp [lam]
lemma lam_comparable (μ : ∀ i,S i → ℝ) (i : ι) (h : (∀ j,S j) → ℝ)
    (s t : ∀ j,S j) (hc : IsComparable i s t) : lam μ i h t=lam μ i h s := by
  rw [← update_comparable i s t hc,lam_update]
lemma delta_projection (μ : ∀ i,S i → ℝ) (γ : ι → (∀ j,S j) → ℝ)
    (hγ : ∀ i s a,γ i (Function.update s i a)=γ i s)
    (i : ι) (h : (∀ j,S j) → ℝ) :
    delta μ i (coScale γ i (proj μ i h))=delta μ i (coScale γ i h) := by
  classical
  funext s t
  unfold delta
  by_cases hc : IsComparable i s t
  · have hgt : γ i t=γ i s := by rw [← update_comparable i s t hc];exact hγ i s (t i)
    have hlt := lam_comparable μ i h s t hc
    simp only [coScale,proj]
    rw [hgt,hlt]
    ring
  · simp [W,hc]
lemma embed_projection (μ : ∀ i,S i → ℝ) (γ : ι → (∀ j,S j) → ℝ)
    (hγ : ∀ i s a,γ i (Function.update s i a)=γ i s) (g : Game ι S) :
    embed μ γ (projGame μ g)=embed μ γ g := by
  funext s t
  unfold embed projGame
  apply Finset.sum_congr rfl
  intro i hi
  exact congrFun (congrFun (delta_projection μ γ hγ i (g i)) s) t
lemma zero_game_control (μ : ∀ i,S i → ℝ) (γ : ι → (∀ j,S j) → ℝ) :
    embed μ γ (0 : Game ι S)=0 := by
  funext s t
  simp [embed,delta,coScale]
lemma diagonal_control (μ : ∀ i,S i → ℝ) (γ : ι → (∀ j,S j) → ℝ) (g : Game ι S) (s : ∀ i,S i) :
    embed μ γ g s s=0 := by simp [embed,delta]
lemma own_coordinate_weight_control :
    let μ : (i : Fin 1) → (fun _ => Bool) i → ℝ := fun _ _ => 1
    let γ : Fin 1 → (Fin 1 → Bool) → ℝ := fun _ s => if s 0 then 2 else 1
    let g : Game (Fin 1) (fun _ => Bool) := fun _ _ => 1
    embed μ γ (projGame μ g) (fun _ => false) (fun _ => true)=0 ∧
    embed μ γ g (fun _ => false) (fun _ => true)=1 := by
  norm_num [embed,projGame,proj,lam,normalized,mass,coScale,delta,W,IsComparable,productMeasureExcept]
end Queelius.GameProjection
open DecompGames.Duplication in
 theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ i,Fintype (S i)] [∀ i,DecidableEq (S i)]
    (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ i,S i) → ℝ) (hγ : IsCoMeasureVec γ) :
    ∀ g : Game ι S,embed μ γ (projGame μ g)=embed μ γ g :=
  fun g => Queelius.GameProjection.embed_projection μ γ hγ.2 g
