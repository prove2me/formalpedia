-- Prove2me | solution 1 for DecompGames.Duplication.proposition_2_10
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T05:21:58.472685+00:00
-- url     : https://prove2.me/submissions/6decd6a9-4889-4cb3-b862-9db6646516ac

import Mathlib
import Definitions.Def_DecompGames_Duplication_Operators
open Finset
namespace Queelius.GameOrthogonal
open DecompGames.Duplication
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
  [∀ i,Fintype (S i)] [∀ i,DecidableEq (S i)]
lemma lam_update (μ : ∀ i,S i → ℝ) (i : ι) (h : (∀ j,S j) → ℝ) (s : ∀ j,S j) (a : S i) :
    lam μ i h (Function.update s i a)=lam μ i h s := by simp [lam]
lemma mass_pos (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (i : ι) (s : ∀ j,S j) : 0 < mass μ i := by
  apply Finset.sum_pos (fun a _ => hμ i a)
  exact ⟨s i,Finset.mem_univ _⟩
lemma normalized_sum (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (i : ι) (s : ∀ j,S j) :
    ∑ a,normalized μ i a=1 := by
  simp only [normalized,← Finset.sum_div]
  exact div_self (ne_of_gt (mass_pos μ hμ i s))
lemma lam_linear (μ : ∀ i,S i → ℝ) (i : ι) : IsLinearMap ℝ (lam μ i) := by
  constructor
  · intro h g;funext s;simp [lam,mul_add,Finset.sum_add_distrib]
  · intro c h;funext s;simp [lam,Finset.mul_sum,mul_left_comm]
lemma proj_linear (μ : ∀ i,S i → ℝ) (i : ι) : IsLinearMap ℝ (proj μ i) := by
  constructor
  · intro h g
    have hl := (lam_linear μ i).map_add h g
    funext s
    change (h s+g s)-lam μ i (h+g) s=(h s-lam μ i h s)+(g s-lam μ i g s)
    rw [hl];simp only [Pi.add_apply];ring
  · intro c h
    have hl := (lam_linear μ i).map_smul c h
    funext s
    change c*h s-lam μ i (c • h) s=c*(h s-lam μ i h s)
    rw [hl];simp only [Pi.smul_apply,smul_eq_mul];ring
lemma lam_fixed (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (i : ι) (h : (∀ j,S j) → ℝ)
    (hh : IsNSGi i h) : lam μ i h=h := by
  funext s
  unfold lam
  simp_rw [show ∀ s a,h (Function.update s i a)=h s from hh]
  rw [← Finset.sum_mul,normalized_sum μ hμ i s,one_mul]
lemma lam_idem (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (i : ι) (h : (∀ j,S j) → ℝ) :
    lam μ i (lam μ i h)=lam μ i h := lam_fixed μ hμ i _ (lam_update μ i h)
lemma proj_idem (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (i : ι) (h : (∀ j,S j) → ℝ) :
    proj μ i (proj μ i h)=proj μ i h := by
  have hz : lam μ i (proj μ i h)=0 := by
    change lam μ i (h-lam μ i h)=0
    rw [(lam_linear μ i).map_sub,lam_idem μ hμ i,sub_self]
  funext s
  simp [proj,hz]
lemma noG_iff (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (i : ι) (h : (∀ j,S j) → ℝ) :
    IsNoGi μ i h ↔ lam μ i h=0 := by
  have eqn (s : ∀ j,S j) : lam μ i h s=(∑ a,μ i a*h (Function.update s i a))/mass μ i := by
    simp [lam,normalized,div_mul_eq_mul_div,Finset.sum_div]
  constructor
  · intro hh;funext s;rw [eqn,hh s];simp
  · intro hh s
    have he := congrFun hh s
    rw [eqn] at he
    exact (div_eq_zero_iff).mp he |>.resolve_right (ne_of_gt (mass_pos μ hμ i s))
lemma nsG_iff (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (i : ι) (h : (∀ j,S j) → ℝ) :
    IsNSGi i h ↔ h ∈ Set.range (lam μ i) := by
  constructor
  · intro hh;exact ⟨h,lam_fixed μ hμ i h hh⟩
  · rintro ⟨g,rfl⟩;exact lam_update μ i g
lemma product_update (μ : ∀ i,S i → ℝ) (i : ι) (s : ∀ j,S j) (a : S i) :
    productMeasure μ (Function.update s i a)=productMeasureExcept μ i s*μ i a := by
  unfold productMeasure productMeasureExcept
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp only [Finset.mem_erase,Finset.mem_univ,true_and] at hj
  rw [Function.update_of_ne hj.1]
lemma weighted_zero (μ : ∀ i,S i → ℝ) (i : ι) (h q : (∀ j,S j) → ℝ)
    (hh : IsNoGi μ i h) (hq : IsNSGi i q) : ip0 μ h q=0 := by
  classical
  by_cases he : Nonempty (∀ j,S j)
  · let s₀ := Classical.choice he
    let e := Equiv.piSplitAt i S
    have hu (a : S i) (t : ∀ j : {j // j ≠ i},S j) :
        e.symm (a,t)=Function.update (e.symm (s₀ i,t)) i a := by
      funext j
      by_cases hj : j=i
      · subst j;simp [e,Equiv.piSplitAt]
      · simp [e,Equiv.piSplitAt,hj,Function.update_of_ne hj]
    unfold ip0
    rw [← e.symm.sum_comp,Fintype.sum_prod_type,Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro t _
    have hs := hh (e.symm (s₀ i,t))
    calc
      _ = productMeasureExcept μ i (e.symm (s₀ i,t))*q (e.symm (s₀ i,t))*
          (∑ a,μ i a*h (Function.update (e.symm (s₀ i,t)) i a)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [hu a t,product_update,hq]
        ring
      _ = 0 := by rw [hs];ring
  · letI : IsEmpty (∀ j,S j) := not_nonempty_iff.mp he
    simp [ip0]
lemma orthogonal (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ j,S j) → ℝ) (hγ : IsCoMeasureVec γ) (i : ι)
    (hKer hIm : (∀ j,S j) → ℝ) (hk : lam μ i hKer=0) (hi : hIm ∈ Set.range (lam μ i)) :
    ip0 μ (coScale γ i hKer) (coScale γ i hIm)=0 := by
  have hqi : IsNSGi i (fun s => γ i s*γ i s*hIm s) := by
    intro s a
    dsimp only
    rw [hγ.2 i s a,(nsG_iff μ hμ i hIm).mpr hi s a]
  have hz := weighted_zero μ i hKer (fun s => γ i s*γ i s*hIm s) ((noG_iff μ hμ i hKer).mpr hk) hqi
  convert hz using 1
  unfold ip0 coScale
  apply Finset.sum_congr rfl
  intro s _
  ring
lemma own_weight_orthogonality_control :
    let μ : (i : Fin 1) → (fun _ => Bool) i → ℝ := fun _ _ => 1
    let γ : Fin 1 → (Fin 1 → Bool) → ℝ := fun _ s => if s 0 then 2 else 1
    let h : (Fin 1 → Bool) → ℝ := fun s => if s 0 then 1 else -1
    lam μ 0 h=0 ∧ ip0 μ (coScale γ 0 h) (coScale γ 0 (fun _ => 1))=3 := by
  constructor
  · funext s;norm_num [lam,normalized,mass]
  · dsimp only
    unfold ip0
    rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
    norm_num [coScale,productMeasure,Equiv.funUnique,Equiv.piUnique]
lemma singleton_projection_control :
    let μ : (i : Fin 1) → (fun _ => Unit) i → ℝ := fun _ _ => 2
    ∀ h : (Fin 1 → Unit) → ℝ,lam μ 0 h=h ∧ proj μ 0 h=0 := by
  intro μ h
  constructor
  · funext s;simp [lam,normalized,mass]
  · funext s;simp [proj,lam,normalized,mass]
end Queelius.GameOrthogonal

namespace DecompGames.Duplication

open Finset

/-- Lemma A.1, p. 24: `Λⁱ` and `Πⁱ` are (linear, idempotent) projections of `C₀`; `γⁱ`-scaled
kernel and image of `Λⁱ` are `⟨·,·⟩₀`-orthogonal; `NoGⁱ = Ker Λⁱ` and `NSGⁱ = Im Λⁱ`. -/
theorem _root_.coordinate_projection_solution {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ i, S i) → ℝ) (hγ : IsCoMeasureVec γ) (i : ι) :
    ((IsLinearMap ℝ (lam μ i) ∧ IsLinearMap ℝ (proj μ i)) ∧
      (lam μ i ∘ lam μ i = lam μ i ∧ proj μ i ∘ proj μ i = proj μ i)) ∧
    (∀ hKer hIm : (∀ j, S j) → ℝ, lam μ i hKer = 0 → hIm ∈ Set.range (lam μ i) →
      ip0 μ (coScale γ i hKer) (coScale γ i hIm) = 0) ∧
    ((∀ h : (∀ j, S j) → ℝ, IsNoGi μ i h ↔ lam μ i h = 0) ∧
      (∀ h : (∀ j, S j) → ℝ, IsNSGi i h ↔ h ∈ Set.range (lam μ i))) := by
  constructor
  · constructor
    · exact ⟨Queelius.GameOrthogonal.lam_linear μ i,Queelius.GameOrthogonal.proj_linear μ i⟩
    · constructor
      · funext h;exact Queelius.GameOrthogonal.lam_idem μ hμ i h
      · funext h;exact Queelius.GameOrthogonal.proj_idem μ hμ i h
  · constructor
    · exact Queelius.GameOrthogonal.orthogonal μ hμ γ hγ i
    · exact ⟨Queelius.GameOrthogonal.noG_iff μ hμ i,Queelius.GameOrthogonal.nsG_iff μ hμ i⟩

end DecompGames.Duplication

namespace Queelius.GameOrthogonal
open DecompGames.Duplication
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
  [∀ i,Fintype (S i)] [∀ i,DecidableEq (S i)]
lemma lam_proj_zero (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (i : ι) (h : (∀ j,S j) → ℝ) :
    lam μ i (proj μ i h)=0 := by
  change lam μ i (h-lam μ i h)=0
  rw [(lam_linear μ i).map_sub,lam_idem μ hμ i,sub_self]
lemma normalized_game_iff (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (g : Game ι S) :
    IsNormalized μ g ↔ lamGame μ g=0 := by
  constructor
  · intro hg;funext i
    exact (noG_iff μ hμ i (g i)).mp (hg i)
  · intro hg i
    exact (noG_iff μ hμ i (g i)).mpr (congrFun hg i)
lemma nonstrategic_game_iff (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (g : Game ι S) :
    IsNonstrategic g ↔ g ∈ Set.range (lamGame μ) := by
  constructor
  · intro hg
    refine ⟨g,?_⟩
    funext i
    exact lam_fixed μ hμ i (g i) (hg i)
  · rintro ⟨h,rfl⟩ i
    exact lam_update μ i (h i)
lemma lamGame_linear (μ : ∀ i,S i → ℝ) : IsLinearMap ℝ (lamGame μ) := by
  constructor
  · intro g h;funext i
    exact (lam_linear μ i).map_add (g i) (h i)
  · intro c g;funext i
    exact (lam_linear μ i).map_smul c (g i)
lemma projGame_linear (μ : ∀ i,S i → ℝ) : IsLinearMap ℝ (projGame μ) := by
  constructor
  · intro g h;funext i
    exact (proj_linear μ i).map_add (g i) (h i)
  · intro c g;funext i
    exact (proj_linear μ i).map_smul c (g i)
lemma lamGame_idem (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (g : Game ι S) :
    lamGame μ (lamGame μ g)=lamGame μ g := by
  funext i;exact lam_idem μ hμ i (g i)
lemma projGame_idem (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (g : Game ι S) :
    projGame μ (projGame μ g)=projGame μ g := by
  funext i;exact proj_idem μ hμ i (g i)
lemma ip0_comm (μ : ∀ i,S i → ℝ) (h g : (∀ j,S j) → ℝ) : ip0 μ h g=ip0 μ g h := by
  unfold ip0;apply Finset.sum_congr rfl;intro s _;ring
lemma game_orthogonal (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ j,S j) → ℝ) (hγ : IsCoMeasureVec γ) (g h : Game ι S) :
    ipGame μ γ (lamGame μ g) (projGame μ h)=0 := by
  unfold ipGame
  apply Finset.sum_eq_zero
  intro i _
  have hz := orthogonal μ hμ γ hγ i (proj μ i (h i)) (lam μ i (g i))
    (lam_proj_zero μ hμ i (h i)) ⟨g i,rfl⟩
  rw [ip0_comm] at hz
  change mass μ i * ip0 μ (coScale γ i (lam μ i (g i))) (coScale γ i (proj μ i (h i)))=0
  rw [hz,mul_zero]
end Queelius.GameOrthogonal

namespace DecompGames.Duplication

open Finset

/-- Lemma A.2, p. 25: (a) `NoG = {g : ∀ i, gⁱ ∈ NoGⁱ} = Ker Λ` (A.7) and
`NSG = {g : ∀ i, gⁱ ∈ NSGⁱ} = Im Λ` (A.8); (b) `Π` and `Λ` are orthogonal projections of `G` for
`⟨·,·⟩_{μ,γ}`. -/
theorem _root_.prior_game_projection_solution {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ i, S i) → ℝ) (hγ : IsCoMeasureVec γ) :
    (∀ g : Game ι S, ((IsNormalized μ g ↔ ∀ i, IsNoGi μ i (g i)) ∧
        (IsNormalized μ g ↔ lamGame μ g = 0)) ∧
      ((IsNonstrategic g ↔ ∀ i, IsNSGi i (g i)) ∧
        (IsNonstrategic g ↔ g ∈ Set.range (lamGame μ)))) ∧
    ((IsLinearMap ℝ (lamGame μ) ∧ IsLinearMap ℝ (projGame μ)) ∧
      (lamGame μ ∘ lamGame μ = lamGame μ ∧ projGame μ ∘ projGame μ = projGame μ) ∧
      ∀ g₁ g₂ : Game ι S, ipGame μ γ (lamGame μ g₁) (projGame μ g₂) = 0) := by
  constructor
  · intro g
    exact ⟨⟨Iff.rfl,Queelius.GameOrthogonal.normalized_game_iff μ hμ g⟩,
      ⟨Iff.rfl,Queelius.GameOrthogonal.nonstrategic_game_iff μ hμ g⟩⟩
  · refine ⟨⟨Queelius.GameOrthogonal.lamGame_linear μ,Queelius.GameOrthogonal.projGame_linear μ⟩,⟨?_,?_⟩,?_⟩
    · funext g;exact Queelius.GameOrthogonal.lamGame_idem μ hμ g
    · funext g;exact Queelius.GameOrthogonal.projGame_idem μ hμ g
    · exact Queelius.GameOrthogonal.game_orthogonal μ hμ γ hγ

end DecompGames.Duplication

namespace Queelius.GameOrthogonal
open DecompGames.Duplication
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
  [∀ i,Fintype (S i)] [∀ i,DecidableEq (S i)]
lemma normalized_projection (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (g : Game ι S) :
    IsNormalized μ (projGame μ g) := by
  apply (normalized_game_iff μ hμ _).mpr
  funext i
  exact lam_proj_zero μ hμ i (g i)
lemma nonstrategic_average (μ : ∀ i,S i → ℝ) (g : Game ι S) :
    IsNonstrategic (lamGame μ g) := fun i => lam_update μ i (g i)
lemma average_fixed_game (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (g : Game ι S)
    (hg : IsNonstrategic g) : lamGame μ g=g := by
  funext i
  exact lam_fixed μ hμ i (g i) (hg i)
lemma normalized_nonstrategic_unique (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (g : Game ι S) :
    ∃! ab : Game ι S × Game ι S,IsNormalized μ ab.1 ∧ IsNonstrategic ab.2 ∧ g=ab.1+ab.2 := by
  refine ⟨(projGame μ g,lamGame μ g),⟨normalized_projection μ hμ g,nonstrategic_average μ g,?_⟩,?_⟩
  · funext i s
    simp [projGame,lamGame,proj]
  · rintro ⟨a,b⟩ ⟨ha,hb,hgab⟩
    have hbval : b=lamGame μ g := by
      rw [hgab,(lamGame_linear μ).map_add,(normalized_game_iff μ hμ a).mp ha,average_fixed_game μ hμ b hb,zero_add]
    have haval : a=projGame μ g := by
      funext i s
      have he := congrFun (congrFun hgab i) s
      rw [hbval] at he
      change a i s=g i s-lam μ i (g i) s
      change g i s=a i s+lam μ i (g i) s at he
      linarith
    exact Prod.ext haval hbval
lemma normalized_nonstrategic_orthogonal (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ j,S j) → ℝ) (hγ : IsCoMeasureVec γ) (a b : Game ι S)
    (ha : IsNormalized μ a) (hb : IsNonstrategic b) : ipGame μ γ a b=0 := by
  unfold ipGame
  apply Finset.sum_eq_zero
  intro i _
  rw [orthogonal μ hμ γ hγ i (a i) (b i) ((noG_iff μ hμ i (a i)).mp (ha i))
    ((nsG_iff μ hμ i (b i)).mp (hb i)),mul_zero]
end Queelius.GameOrthogonal

namespace DecompGames.Duplication

open Finset

/-- Proposition 2.10, p. 10, (2.16): `G = μ-NoG ⊕_{μ,γ} NSG`. Every game is uniquely the sum of a
`μ`-normalized and a nonstrategic game, and the two classes are `⟨·,·⟩_{μ,γ}`-orthogonal. -/
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ i, S i) → ℝ) (hγ : IsCoMeasureVec γ) :
    (∀ g : Game ι S, ∃! ab : Game ι S × Game ι S,
      IsNormalized μ ab.1 ∧ IsNonstrategic ab.2 ∧ g = ab.1 + ab.2) ∧
    ∀ a b : Game ι S, IsNormalized μ a → IsNonstrategic b → ipGame μ γ a b = 0 := by
  exact ⟨Queelius.GameOrthogonal.normalized_nonstrategic_unique μ hμ,Queelius.GameOrthogonal.normalized_nonstrategic_orthogonal μ hμ γ hγ⟩

end DecompGames.Duplication
