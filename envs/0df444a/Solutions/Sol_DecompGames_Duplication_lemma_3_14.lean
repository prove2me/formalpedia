-- Prove2me | solution 1 for DecompGames.Duplication.lemma_3_14
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T07:47:33.972222+00:00
-- url     : https://prove2.me/submissions/4dbefe4a-dd4b-49b6-a1de-237d879d4bb6

import Mathlib
import Definitions.Def_DecompGames_Duplication_Extension
open DecompGames.Duplication
open Finset
namespace Queelius.GameExtension
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S S' : ι → Type}
  [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
  [∀ i, Fintype (S' i)] [∀ i, DecidableEq (S' i)]
lemma collapse_update (π : ∀ i, S' i → S i) (s : ∀ i,S' i) (i : ι) (a : S' i) :
    (fun j => π j (Function.update s i a j)) = Function.update (fun j => π j (s j)) i (π i a) := by
  funext j
  by_cases h : j=i
  · subst j; simp
  · simp [Function.update_of_ne h]
lemma weighted_sum (π : ∀ i, S' i → S i) (μ : ∀ i,S i → ℝ) (μ' : ∀ i,S' i → ℝ)
    (hext : IsMeasureExtension π μ μ') (i : ι) (f : S i → ℝ) :
    ∑ b, μ' i b * f (π i b) = ∑ a, μ i a * f a := by
  classical
  calc
    ∑ b, μ' i b * f (π i b) = ∑ a, ∑ b ∈ univ.filter (fun b => π i b=a), μ' i b * f a := by
      symm
      calc
        _ = ∑ a, ∑ b ∈ univ.filter (fun b => π i b=a), μ' i b * f (π i b) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b hb
          rw [(Finset.mem_filter.mp hb).2]
        _ = _ := by rw [Finset.sum_fiberwise_eq_sum_filter];simp
    _ = ∑ a, μ i a * f a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_mul,hext i a]
lemma potential (π : ∀ i, S' i → S i) (γ : ι → (∀ i,S i) → ℝ) (g : Game ι S)
    (hg : IsPotential γ g) : IsPotential (extend π γ) (extend π g) := by
  obtain ⟨φ,hφ⟩ := hg
  refine ⟨fun s => φ (fun j => π j (s j)),?_⟩
  intro i s a b
  simpa only [extend,collapse_update] using hφ i (fun j => π j (s j)) (π i a) (π i b)
lemma nonstrategic (π : ∀ i, S' i → S i) (g : Game ι S) (hg : IsNonstrategic g) :
    IsNonstrategic (extend π g) := by
  intro i s a
  simpa only [extend,collapse_update] using hg i (fun j => π j (s j)) (π i a)
lemma normalized (π : ∀ i, S' i → S i) (μ : ∀ i,S i → ℝ) (μ' : ∀ i,S' i → ℝ)
    (hext : IsMeasureExtension π μ μ') (g : Game ι S) (hg : IsNormalized μ g) :
    IsNormalized μ' (extend π g) := by
  intro i s
  simp only [extend,collapse_update]
  exact (weighted_sum π μ μ' hext i
    (fun a => g i (Function.update (fun j => π j (s j)) i a))).trans
      (hg i (fun j => π j (s j)))
lemma harmonic (π : ∀ i, S' i → S i) (μ : ∀ i,S i → ℝ) (μ' : ∀ i,S' i → ℝ)
    (hext : IsMeasureExtension π μ μ') (γ : ι → (∀ i,S i) → ℝ) (g : Game ι S)
    (hg : IsHarmonic μ γ g) : IsHarmonic μ' (extend π γ) (extend π g) := by
  intro s
  calc
    _ = ∑ i,∑ a, μ i a * γ i (fun j => π j (s j)) *
        (g i (fun j => π j (s j))-g i (Function.update (fun j => π j (s j)) i a)) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [extend,collapse_update]
      simpa only [mul_assoc] using weighted_sum π μ μ' hext i
        (fun a => γ i (fun j => π j (s j)) *
          (g i (fun j => π j (s j))-g i (Function.update (fun j => π j (s j)) i a)))
    _ = 0 := hg (fun j => π j (s j))
lemma coMeasure (π : ∀ i, S' i → S i) (γ : ι → (∀ i,S i) → ℝ)
    (hγ : IsCoMeasureVec γ) : IsCoMeasureVec (extend π γ) := by
  refine ⟨fun i s => hγ.1 i (fun j => π j (s j)),?_⟩
  intro i s a
  simpa only [extend,collapse_update] using hγ.2 i (fun j => π j (s j)) (π i a)
lemma decomposition (π : ∀ i, S' i → S i) (μ : ∀ i,S i → ℝ) (μ' : ∀ i,S' i → ℝ)
    (hext : IsMeasureExtension π μ μ') (γ : ι → (∀ i,S i) → ℝ)
    (g n p h : Game ι S) (hg : IsDecomposition μ γ g n p h) :
    IsDecomposition μ' (extend π γ) (extend π g) (extend π n) (extend π p) (extend π h) := by
  obtain ⟨hn,⟨hpn,hpp⟩,⟨hhn,hhh⟩,hs⟩ := hg
  refine ⟨nonstrategic π n hn,⟨normalized π μ μ' hext p hpn,potential π γ p hpp⟩,
    ⟨normalized π μ μ' hext h hhn,harmonic π μ μ' hext γ h hhh⟩,?_⟩
  rw [hs]
  rfl
lemma extend_identity (g : Game ι S) : extend (fun _ => id) g=g := rfl
lemma extend_zero (π : ∀ i,S' i → S i) : extend π (0 : Game ι S)=0 := rfl
lemma split_mass_control :
    (∑ b : Fin 3,(if b=2 then (1:ℝ) else 1/2)*(if b=2 then (-1:ℝ) else 1))=0 ∧
    (∑ b : Fin 3,(1:ℝ)*(if b=2 then (-1:ℝ) else 1))=1 := by
  norm_num [Fin.sum_univ_succ,Fin.ext_iff]
end Queelius.GameExtension

namespace DecompGames.Duplication

open Finset

/-- Lemma 3.14, p. 18, for an extension along any collapsing map `π` (a single duplication is the
case of Definition 3.13), with the extended co-measure `γ̌ = Ť(γ)` (`γ̌ʲ(s') = γʲ(π(s'))`):
(i) `γ`-potential ⇒ `ǧ` is `γ̌`-potential; (ii) nonstrategic ⇒ `ǧ` nonstrategic;
(iii) `μ`-normalized ⇒ `ǧ` is `μ̌`-normalized; (iv) `(μ, γ)`-harmonic ⇒ `ǧ` is `(μ̌, γ̌)`-harmonic. -/
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {S S' : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, Fintype (S' i)] [∀ i, DecidableEq (S' i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ i, S i) → ℝ) (hγ : IsCoMeasureVec γ)
    (π : ∀ i, S' i → S i) (μ' : ∀ i, S' i → ℝ) (hμ' : IsMeasureVec μ')
    (hext : IsMeasureExtension π μ μ') (g : Game ι S) :
    (IsPotential γ g → IsPotential (extend π γ) (extend π g)) ∧
    (IsNonstrategic g → IsNonstrategic (extend π g)) ∧
    (IsNormalized μ g → IsNormalized μ' (extend π g)) ∧
    (IsHarmonic μ γ g → IsHarmonic μ' (extend π γ) (extend π g)) := by
  exact ⟨Queelius.GameExtension.potential π γ g,Queelius.GameExtension.nonstrategic π g,
    Queelius.GameExtension.normalized π μ μ' hext g,
    Queelius.GameExtension.harmonic π μ μ' hext γ g⟩

end DecompGames.Duplication
