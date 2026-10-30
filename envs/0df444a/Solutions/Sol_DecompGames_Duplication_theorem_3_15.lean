-- Prove2me | solution 1 for DecompGames.Duplication.theorem_3_15
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T07:51:41.343464+00:00
-- url     : https://prove2.me/submissions/904d6852-1df5-41e9-83d1-20d7cd35bd76

import Mathlib
import Definitions.Def_DecompGames_Duplication_Operators
import Definitions.Def_DecompGames_Duplication_Extension
section
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
theorem _root_.normalized_split_solution {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ i, S i) → ℝ) (hγ : IsCoMeasureVec γ) :
    (∀ g : Game ι S, ∃! ab : Game ι S × Game ι S,
      IsNormalized μ ab.1 ∧ IsNonstrategic ab.2 ∧ g = ab.1 + ab.2) ∧
    ∀ a b : Game ι S, IsNormalized μ a → IsNonstrategic b → ipGame μ γ a b = 0 := by
  exact ⟨Queelius.GameOrthogonal.normalized_nonstrategic_unique μ hμ,Queelius.GameOrthogonal.normalized_nonstrategic_orthogonal μ hμ γ hγ⟩

end DecompGames.Duplication

namespace Queelius.GameAdjoint
open DecompGames.Duplication
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
  [∀ i,Fintype (S i)] [∀ i,DecidableEq (S i)]
lemma comparable_symm (i : ι) (s t : ∀ j,S j) (h : IsComparable i s t) : IsComparable i t s := by
  exact ⟨Ne.symm h.1,fun j hj => (h.2 j hj).symm⟩
lemma except_comparable (μ : ∀ i,S i → ℝ) (i : ι) (s t : ∀ j,S j) (h : IsComparable i s t) :
    productMeasureExcept μ i s=productMeasureExcept μ i t := by
  unfold productMeasureExcept
  apply Finset.prod_congr rfl
  intro j hj
  rw [h.2 j (Finset.mem_erase.mp hj).1]
lemma W_symm (μ : ∀ i,S i → ℝ) (i : ι) (s t : ∀ j,S j) : W μ i s t=W μ i t s := by
  classical
  by_cases hc : IsComparable i s t
  · rw [W,W,if_pos hc,if_pos (comparable_symm i s t hc),except_comparable μ i s t hc]
  · have hn : ¬ IsComparable i t s := fun ht => hc (comparable_symm i t s ht)
    simp [W,hc,hn]
lemma product_positive (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (s : ∀ j,S j) :
    0 < productMeasure μ s := Finset.prod_pos (fun j _ => hμ j (s j))
lemma ip0_separates (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (f g : (∀ j,S j) → ℝ)
    (h : ∀ a,ip0 μ a f=ip0 μ a g) : f=g := by
  classical
  funext s
  have hs := h (fun x => if x=s then 1 else 0)
  simp [ip0,mul_ite,ite_mul] at hs
  exact hs.resolve_right (ne_of_gt (product_positive μ hμ s))
lemma adjoint_identity (μ : ∀ i,S i → ℝ) (i : ι) (X : (∀ j,S j) → (∀ j,S j) → ℝ)
    (hX : IsFlow X) (h : (∀ j,S j) → ℝ) : ip1 μ (delta μ i h) X=ip0 μ h (deltaStar μ i X) := by
  let A := ∑ s,∑ t,productMeasure μ s*productMeasure μ t*W μ i s t*h t*X s t
  let B := ∑ s,∑ t,productMeasure μ s*productMeasure μ t*W μ i s t*h s*X s t
  have hab : A= -B := by
    dsimp [A,B]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    rw [W_symm μ i t s,hX t s]
    ring
  have hs : (∑ s,∑ t,productMeasure μ s*productMeasure μ t*(W μ i s t*(h t-h s))*X s t)=A-B := by
    dsimp [A,B]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hb : ip0 μ h (deltaStar μ i X)= -B := by
    unfold ip0 deltaStar
    dsimp [B]
    simp_rw [mul_neg,Finset.mul_sum,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring
  unfold ip1 delta
  rw [hs,hab,hb]
  ring
lemma except_positive (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (i : ι) (s : ∀ j,S j) :
    0 < productMeasureExcept μ i s := Finset.prod_pos (fun j _ => hμ j (s j))
lemma product_comparable (μ : ∀ i,S i → ℝ) (i : ι) (s t : ∀ j,S j) (hc : IsComparable i s t) :
    productMeasure μ t=productMeasureExcept μ i s*μ i (t i) := by
  unfold productMeasure productMeasureExcept
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [hc.2 j (Finset.mem_erase.mp hj).1]
lemma edge_weight_formula (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (i : ι)
    (s t : ∀ j,S j) (hc : IsComparable i s t) :
    productMeasure μ t*W μ i s t=μ i (t i)*Real.sqrt (productMeasureExcept μ i s) := by
  rw [W,if_pos hc,product_comparable μ i s t hc]
  have hp := except_positive μ hμ i s
  have hn := ne_of_gt (Real.sqrt_pos.mpr hp)
  have hs := Real.mul_self_sqrt hp.le
  have he := congrArg (fun x => μ i (t i)*x) hs
  field_simp [hn] <;> nlinarith [he]
open Classical in
lemma adjoint_explicit (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (i : ι)
    (X : (∀ j,S j) → (∀ j,S j) → ℝ) (s : ∀ j,S j) :
    deltaStar μ i X s= -∑ t ∈ Finset.univ.filter (fun t => IsComparable i s t),
      μ i (t i)*Real.sqrt (productMeasureExcept μ i s)*X s t := by
  classical
  unfold deltaStar
  rw [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  by_cases hc : IsComparable i s t
  · rw [if_pos hc,edge_weight_formula μ hμ i s t hc]
  · simp [W,hc]
lemma adjoint_unique (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (i : ι)
    (X : (∀ j,S j) → (∀ j,S j) → ℝ) (hX : IsFlow X) (f : (∀ j,S j) → ℝ) :
    (∀ h,ip1 μ (delta μ i h) X=ip0 μ h f) ↔ f=deltaStar μ i X := by
  constructor
  · intro hf
    apply ip0_separates μ hμ
    intro h
    rw [← hf h,adjoint_identity μ i X hX h]
  · rintro rfl h
    exact adjoint_identity μ i X hX h
lemma one_edge_adjoint_control :
    let μ : (i : Fin 1) → (fun _ => Bool) i → ℝ := fun _ _ => 1
    let X : (Fin 1 → Bool) → (Fin 1 → Bool) → ℝ := fun s t =>
      (if t 0 then 1 else 0)-(if s 0 then 1 else 0)
    deltaStar μ 0 X (fun _ => false)= -1 ∧ deltaStar μ 0 X (fun _ => true)=1 := by
  constructor
  all_goals
    dsimp only
    unfold deltaStar
    rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
    norm_num [productMeasure,W,productMeasureExcept,IsComparable,Equiv.funUnique,Equiv.piUnique]
end Queelius.GameAdjoint

namespace DecompGames.Duplication

open Finset

open Classical in
/-- Proposition A.3, p. 27: the adjoint `δⁱ*` of `δⁱ` (for `⟨·,·⟩₁` on flows and `⟨·,·⟩₀` on `C₀`,
(A.14)) is given by (A.15), `δⁱ*X(s) = −∑_{t ∈ S} μ(t) Wⁱ(s, t) X(s, t)`, and (A.15) equals (A.16),
`−∑_{t : (s,t) ∈ Eⁱ} μⁱ(tⁱ) √(μ⁻ⁱ(s⁻ⁱ)) X(s, t)`. -/
theorem _root_.adjoint_solution {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ) (i : ι) :
    (∀ X : (∀ j, S j) → (∀ j, S j) → ℝ, IsFlow X →
      ∀ f : (∀ j, S j) → ℝ,
        (∀ h : (∀ j, S j) → ℝ, ip1 μ (delta μ i h) X = ip0 μ h f) ↔ f = deltaStar μ i X) ∧
    (∀ X : (∀ j, S j) → (∀ j, S j) → ℝ, IsFlow X → ∀ s : ∀ j, S j,
      deltaStar μ i X s =
        -∑ t ∈ univ.filter (fun t => IsComparable i s t),
          μ i (t i) * Real.sqrt (productMeasureExcept μ i s) * X s t) := by
  exact ⟨fun X hX f => Queelius.GameAdjoint.adjoint_unique μ hμ i X hX f,fun X _ s => Queelius.GameAdjoint.adjoint_explicit μ hμ i X s⟩

end DecompGames.Duplication

namespace Queelius.GameDifferential
open DecompGames.Duplication
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
  [∀ i,Fintype (S i)] [∀ i,DecidableEq (S i)]
lemma update_comparable (i : ι) (s t : ∀ j,S j) (hc : IsComparable i s t) :
    Function.update s i (t i)=t := by
  funext j
  by_cases hj : j=i
  · subst j;simp
  · simp only [Function.update_of_ne hj]
    exact hc.2 j hj
lemma comparable_disjoint (i j : ι) (hij : i≠j) (s t : ∀ k,S k)
    (hi : IsComparable i s t) (hj : IsComparable j s t) : False := hi.1 (hj.2 i hij)
lemma cross_zero (μ : ∀ i,S i → ℝ) (i j : ι) (hij : i≠j) (h : (∀ k,S k) → ℝ) :
    deltaStar μ i (delta μ j h)=0 := by
  classical
  funext s
  unfold deltaStar delta
  apply neg_eq_zero.mpr
  apply Finset.sum_eq_zero
  intro t _
  by_cases hi : IsComparable i s t
  · have hj : ¬ IsComparable j s t := fun hj => comparable_disjoint i j hij s t hi hj
    simp [W,hj]
  · simp [W,hi]
lemma star_sum (μ : ∀ i,S i → ℝ) (i : ι) (X : ι → (∀ k,S k) → (∀ k,S k) → ℝ) :
    deltaStar μ i (fun s t => ∑ j,X j s t)=fun s => ∑ j,deltaStar μ i (X j) s := by
  funext s
  unfold deltaStar
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm,Finset.sum_neg_distrib]
lemma star_embed (μ : ∀ i,S i → ℝ) (γ : ι → (∀ k,S k) → ℝ) (g : Game ι S) :
    deltaStarAll μ (embed μ γ g)=fun s => ∑ i,deltaStar μ i (delta μ i (coScale γ i (g i))) s := by
  classical
  funext s
  unfold deltaStarAll embed
  apply Finset.sum_congr rfl
  intro i _
  rw [star_sum]
  dsimp only
  rw [Finset.sum_eq_single i]
  · intro j _ hji
    rw [cross_zero μ i j (Ne.symm hji)]
    rfl
  · simp
lemma coScale_comparable (γ : ι → (∀ j,S j) → ℝ) (hγ : IsCoMeasureVec γ)
    (i : ι) (s t : ∀ j,S j) (hc : IsComparable i s t) : γ i t=γ i s := by
  rw [← update_comparable i s t hc]
  exact hγ.2 i s (t i)
lemma star_delta_coScale (μ : ∀ i,S i → ℝ) (γ : ι → (∀ j,S j) → ℝ) (hγ : IsCoMeasureVec γ)
    (i : ι) (h : (∀ j,S j) → ℝ) :
    deltaStar μ i (delta μ i (coScale γ i h))=coScale γ i (deltaStar μ i (delta μ i h)) := by
  classical
  funext s
  unfold deltaStar delta coScale
  change -(∑ t,productMeasure μ t*W μ i s t*(W μ i s t*(γ i t*h t-γ i s*h s)))=
    γ i s*(-(∑ t,productMeasure μ t*W μ i s t*(W μ i s t*(h t-h s))))
  calc
    _ = -(∑ t,γ i s*(productMeasure μ t*W μ i s t*(W μ i s t*(h t-h s)))) := by
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      by_cases hc : IsComparable i s t
      · rw [coScale_comparable γ hγ i s t hc];ring
      · simp [W,hc]
    _ = _ := by rw [← Finset.mul_sum];ring
end Queelius.GameDifferential

namespace DecompGames.Duplication
open Finset
 theorem _root_.cross_solution {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ i, S i) → ℝ) (hγ : IsCoMeasureVec γ) :
    (∀ i j : ι, i ≠ j → ∀ h : (∀ k, S k) → ℝ, deltaStar μ i (delta μ j h) = 0) ∧
    (∀ g : Game ι S, deltaStarAll μ (embed μ γ g) =
      fun s => ∑ i, deltaStar μ i (delta μ i (coScale γ i (g i))) s) ∧
    (∀ (i : ι) (h : (∀ k, S k) → ℝ),
      deltaStar μ i (delta μ i (coScale γ i h)) = coScale γ i (deltaStar μ i (delta μ i h))) := by
  exact ⟨Queelius.GameDifferential.cross_zero μ,Queelius.GameDifferential.star_embed μ γ,
    Queelius.GameDifferential.star_delta_coScale μ γ hγ⟩
end DecompGames.Duplication

namespace Queelius.GameLaplacian
open DecompGames.Duplication
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
  [∀ i,Fintype (S i)] [∀ i,DecidableEq (S i)]
lemma fiber_sum (i : ι) (s : ∀ j,S j) (F : (∀ j,S j) → ℝ) :
    (∑ t,if (∀ j,j≠i → t j=s j) then F t else 0)=∑ a,F (Function.update s i a) := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun t _ => t i)
  · intro t ht;exact Finset.mem_univ _
  · intro t ht u hu he
    have ht' := (Finset.mem_filter.mp ht).2
    have hu' := (Finset.mem_filter.mp hu).2
    funext j
    by_cases hj : j=i
    · subst j;exact he
    · exact (ht' j hj).trans (hu' j hj).symm
  · intro a _
    refine ⟨Function.update s i a,?_,by simp⟩
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    intro j hj
    exact Function.update_of_ne hj _ _
  · intro t ht
    congr 1
    funext j
    by_cases hj : j=i
    · subst j;simp
    · simp only [Function.update_of_ne hj]
      exact (Finset.mem_filter.mp ht).2 j hj
lemma star_delta_sum (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (i : ι)
    (h : (∀ j,S j) → ℝ) (s : ∀ j,S j) :
    deltaStar μ i (delta μ i h) s=∑ a,μ i a*(h s-h (Function.update s i a)) := by
  classical
  have he (t : ∀ j,S j) :
      -(productMeasure μ t*W μ i s t*(W μ i s t*(h t-h s)))=
        if (∀ j,j≠i → t j=s j) then μ i (t i)*(h s-h t) else 0 := by
    by_cases hc : IsComparable i s t
    · have hf : ∀ j,j≠i → t j=s j := fun j hj => (hc.2 j hj).symm
      rw [if_pos hf,Queelius.GameAdjoint.edge_weight_formula μ hμ i s t hc,W,if_pos hc]
      have hn := (Real.sqrt_pos.mpr (Queelius.GameAdjoint.except_positive μ hμ i s)).ne'
      field_simp [hn] <;> ring
    · by_cases hf : ∀ j,j≠i → t j=s j
      · have ht : t=s := by
          funext j
          by_cases hj : j=i
          · subst j
            by_contra hne
            exact hc ⟨Ne.symm hne,fun k hk => (hf k hk).symm⟩
          · exact hf j hj
        subst t
        simp [W,hc]
      · simp [W,hc,hf]
  unfold deltaStar delta
  rw [← Finset.sum_neg_distrib]
  simp_rw [he]
  rw [fiber_sum]
  simp only [Function.update_self]
lemma laplacian_projection (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (i : ι)
    (h : (∀ j,S j) → ℝ) :
    deltaStar μ i (delta μ i h)=fun s => mass μ i*proj μ i h s := by
  funext s
  rw [star_delta_sum μ hμ i h s]
  have hM := (Queelius.GameOrthogonal.mass_pos μ hμ i s).ne'
  have hl : mass μ i*lam μ i h s=∑ a,μ i a*h (Function.update s i a) := by
    unfold lam normalized
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    field_simp
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib,← Finset.sum_mul]
  change mass μ i*h s-(∑ a,μ i a*h (Function.update s i a))=mass μ i*(h s-lam μ i h s)
  rw [← hl]
  ring
end Queelius.GameLaplacian
namespace DecompGames.Duplication
open Finset
 theorem _root_.laplacian_solution {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ) (i : ι) :
    ∀ h : (∀ j, S j) → ℝ, deltaStar μ i (delta μ i h) = fun s => mass μ i * proj μ i h s := by
  exact Queelius.GameLaplacian.laplacian_projection μ hμ i
end DecompGames.Duplication

namespace Queelius.GameHarmonic
open DecompGames.Duplication Queelius.GameOrthogonal
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
  [∀ i,Fintype (S i)] [∀ i,DecidableEq (S i)]
lemma normalized_fixed (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (g : Game ι S) :
    IsNormalized μ g ↔ projGame μ g=g := by
  constructor
  · intro hg
    have hl := (normalized_game_iff μ hμ g).mp hg
    funext i s
    change g i s-lamGame μ g i s=g i s
    rw [hl]
    simp
  · intro hp
    have hn := normalized_projection μ hμ g
    rw [hp] at hn
    exact hn
lemma harmonic_sum (μ : ∀ i,S i → ℝ) (γ : ι → (∀ j,S j) → ℝ) (g : Game ι S)
    (hg : IsNormalized μ g) (s : ∀ j,S j) :
    (∑ i,∑ a,μ i a*γ i s*(g i s-g i (Function.update s i a)))=
      ∑ i,mass μ i*γ i s*g i s := by
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = γ i s*((∑ a,μ i a)*g i s-(∑ a,μ i a*g i (Function.update s i a))) := by
      calc
        _ = ∑ a,γ i s*(μ i a*g i s-μ i a*g i (Function.update s i a)) := by
          apply Finset.sum_congr rfl
          intro a _
          ring
        _ = _ := by rw [← Finset.mul_sum,Finset.sum_sub_distrib,← Finset.sum_mul]
    _ = _ := by rw [hg i s];unfold mass;ring
lemma normalized_harmonic (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ j,S j) → ℝ) (g : Game ι S) :
    (IsNormalized μ g ∧ IsHarmonic μ γ g) ↔
      ((∀ s,∑ i,mass μ i*γ i s*g i s=0) ∧ projGame μ g=g) := by
  constructor
  · rintro ⟨hn,hh⟩
    exact ⟨fun s => (harmonic_sum μ γ g hn s).symm.trans (hh s),(normalized_fixed μ hμ g).mp hn⟩
  · rintro ⟨hh,hp⟩
    have hn := (normalized_fixed μ hμ g).mpr hp
    exact ⟨hn,fun s => (harmonic_sum μ γ g hn s).trans (hh s)⟩
lemma normalization_needed_control :
    let μ : (i : Fin 1) → (fun _ => Bool) i → ℝ := fun _ _ => 1
    let γ : Fin 1 → (Fin 1 → Bool) → ℝ := fun _ _ => 1
    let g : Game (Fin 1) (fun _ => Bool) := fun _ _ => 1
    IsHarmonic μ γ g ∧ (∑ i,mass μ i*γ i (fun _ => false)*g i (fun _ => false))=2 := by
  constructor
  · intro s;simp
  · norm_num [mass]
end Queelius.GameHarmonic
namespace DecompGames.Duplication
open Finset
 theorem _root_.normalized_harmonic_solution {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ i, S i) → ℝ) (hγ : IsCoMeasureVec γ) :
    ∀ g : Game ι S, (IsNormalized μ g ∧ IsHarmonic μ γ g) ↔
      ((∀ s : ∀ j, S j, ∑ i, mass μ i * γ i s * g i s = 0) ∧ projGame μ g = g) := by
  exact Queelius.GameHarmonic.normalized_harmonic μ hμ γ
end DecompGames.Duplication

namespace Queelius.GameGradientKernel
open DecompGames.Duplication Queelius.GameOrthogonal Queelius.GameLaplacian
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
  [∀ i,Fintype (S i)] [∀ i,DecidableEq (S i)]
lemma projection_eq_of_gradient_eq (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (i : ι)
    (f g : (∀ j,S j) → ℝ) (hδ : delta μ i f=delta μ i g) : proj μ i f=proj μ i g := by
  have hh := congrArg (deltaStar μ i) hδ
  rw [laplacian_projection μ hμ i f,laplacian_projection μ hμ i g] at hh
  funext s
  have hs := congrFun hh s
  exact mul_left_cancel₀ (mass_pos μ hμ i s).ne' hs
lemma projection_of_noG (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (i : ι)
    (f : (∀ j,S j) → ℝ) (hf : IsNoGi μ i f) : proj μ i f=f := by
  have hl := (noG_iff μ hμ i f).mp hf
  funext s
  simp [proj,hl]
lemma ip0_add_left (μ : ∀ i,S i → ℝ) (f g h : (∀ j,S j) → ℝ) :
    ip0 μ (f+g) h=ip0 μ f h+ip0 μ g h := by
  simp [ip0,mul_add,add_mul,Finset.sum_add_distrib]
lemma normalized_gradient_inner (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ) (i : ι)
    (φ φt : (∀ j,S j) → ℝ) (hφ : IsNoGi μ i φ) (hδ : delta μ i φ=delta μ i φt)
    (ψ : (∀ j,S j) → ℝ) (hψ : IsNoGi μ i ψ) : ip0 μ φ ψ=ip0 μ φt ψ := by
  have hp := projection_eq_of_gradient_eq μ hμ i φ φt hδ
  rw [projection_of_noG μ hμ i φ hφ] at hp
  have he : φt=φ+lam μ i φt := by
    funext s
    have hh := congrFun hp s
    change φ s=φt s-lam μ i φt s at hh
    change φt s=φ s+lam μ i φt s
    linarith
  have hz : ip0 μ (lam μ i φt) ψ=0 := by
    rw [ip0_comm]
    exact weighted_zero μ i ψ (lam μ i φt) hψ (lam_update μ i φt)
  rw [he,ip0_add_left,hz,add_zero]
end Queelius.GameGradientKernel
namespace DecompGames.Duplication
open Finset
 theorem _root_.normalized_gradient_inner_solution {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ) (i : ι)
    (φ φt : (∀ j, S j) → ℝ) (hφ : IsNoGi μ i φ) (hδ : delta μ i φ = delta μ i φt) :
    ∀ ψ : (∀ j, S j) → ℝ, IsNoGi μ i ψ → ip0 μ φ ψ = ip0 μ φt ψ := by
  exact Queelius.GameGradientKernel.normalized_gradient_inner μ hμ i φ φt hφ hδ
end DecompGames.Duplication

namespace Queelius.GameTripleOrthogonal
open DecompGames.Duplication Queelius.GameOrthogonal Queelius.GameDifferential Queelius.GameGradientKernel
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
  [∀ i,Fintype (S i)] [∀ i,DecidableEq (S i)]
lemma coScale_noG (μ : ∀ i,S i → ℝ) (γ : ι → (∀ j,S j) → ℝ) (hγ : IsCoMeasureVec γ)
    (i : ι) (f : (∀ j,S j) → ℝ) (hf : IsNoGi μ i f) : IsNoGi μ i (coScale γ i f) := by
  intro s
  calc
    _ = γ i s*(∑ a,μ i a*f (Function.update s i a)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      unfold coScale
      rw [hγ.2 i s a]
      ring
    _ = 0 := by rw [hf s];ring
lemma potential_gradients (μ : ∀ i,S i → ℝ) (γ : ι → (∀ j,S j) → ℝ) (hγ : IsCoMeasureVec γ)
    (g : Game ι S) (φ : (∀ j,S j) → ℝ)
    (hφ : ∀ i (s : ∀ j,S j) (a b : S i),
      γ i s*(g i (Function.update s i b)-g i (Function.update s i a))=
        φ (Function.update s i b)-φ (Function.update s i a)) (i : ι) :
    delta μ i (coScale γ i (g i))=delta μ i φ := by
  classical
  funext s t
  by_cases hc : IsComparable i s t
  · have ht := update_comparable i s t hc
    have hgap : γ i s*(g i t-g i s)=φ t-φ s := by
      simpa only [ht,Function.update_eq_self] using hφ i s (s i) (t i)
    unfold delta coScale
    rw [coScale_comparable γ hγ i s t hc,← mul_sub,hgap]
  · simp [delta,W,hc]
lemma weighted_inner_sum (μ : ∀ i,S i → ℝ) (φ : (∀ j,S j) → ℝ)
    (v : ι → (∀ j,S j) → ℝ) (a : ι → ℝ) :
    (∑ i,a i*ip0 μ φ (v i))=ip0 μ φ (fun s => ∑ i,a i*v i s) := by
  unfold ip0
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  ring
lemma potential_harmonic_orthogonal (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ j,S j) → ℝ) (hγ : IsCoMeasureVec γ) (p h : Game ι S)
    (hnp : IsNormalized μ p) (hpp : IsPotential γ p)
    (hnh : IsNormalized μ h) (hhh : IsHarmonic μ γ h) : ipGame μ γ p h=0 := by
  obtain ⟨φ,hφ⟩ := hpp
  have hp (i : ι) := coScale_noG μ γ hγ i (p i) (hnp i)
  have hh (i : ι) := coScale_noG μ γ hγ i (h i) (hnh i)
  have hi (i : ι) : ip0 μ (coScale γ i (p i)) (coScale γ i (h i))=ip0 μ φ (coScale γ i (h i)) :=
    normalized_gradient_inner μ hμ i (coScale γ i (p i)) φ (hp i)
      (potential_gradients μ γ hγ p φ hφ i) (coScale γ i (h i)) (hh i)
  have hsum := ((Queelius.GameHarmonic.normalized_harmonic μ hμ γ h).mp ⟨hnh,hhh⟩).1
  unfold ipGame
  simp_rw [hi]
  rw [weighted_inner_sum]
  have hz : (fun s => ∑ i,mass μ i*coScale γ i (h i) s)=0 := by
    funext s
    simpa only [coScale,mul_assoc,Pi.zero_apply] using hsum s
  rw [hz]
  simp [ip0]
end Queelius.GameTripleOrthogonal
namespace DecompGames.Duplication
open Finset
 theorem _root_.triple_orthogonality_solution {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ i, S i) → ℝ) (hγ : IsCoMeasureVec γ) :
    (∀ p h : Game ι S, IsNormalized μ p → IsPotential γ p →
      IsNormalized μ h → IsHarmonic μ γ h → ipGame μ γ p h = 0) ∧
    (∀ p n : Game ι S, IsNormalized μ p → IsPotential γ p →
      IsNonstrategic n → ipGame μ γ p n = 0) ∧
    (∀ h n : Game ι S, IsNormalized μ h → IsHarmonic μ γ h →
      IsNonstrategic n → ipGame μ γ h n = 0) := by
  exact ⟨Queelius.GameTripleOrthogonal.potential_harmonic_orthogonal μ hμ γ hγ,
    fun p n hp _ hn => Queelius.GameOrthogonal.normalized_nonstrategic_orthogonal μ hμ γ hγ p n hp hn,
    fun h n hh _ hn => Queelius.GameOrthogonal.normalized_nonstrategic_orthogonal μ hμ γ hγ h n hh hn⟩
end DecompGames.Duplication

namespace Queelius.GameFlowClasses
open DecompGames.Duplication Queelius.GameOrthogonal Queelius.GameAdjoint
open Queelius.GameDifferential Queelius.GameLaplacian Queelius.GameTripleOrthogonal
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
  [∀ i,Fintype (S i)] [∀ i,DecidableEq (S i)]
lemma sum_on_comparable (μ : ∀ i,S i → ℝ) (v : ι → (∀ j,S j) → ℝ)
    (i : ι) (s t : ∀ j,S j) (hc : IsComparable i s t) :
    (∑ j,delta μ j (v j) s t)=delta μ i (v i) s t := by
  classical
  apply Finset.sum_eq_single i
  · intro j _ hji
    have hj : ¬ IsComparable j s t := fun hh => comparable_disjoint i j (Ne.symm hji) s t hc hh
    simp [delta,W,hj]
  · simp
lemma potential_identity_of_embedding (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ j,S j) → ℝ) (hγ : IsCoMeasureVec γ) (g : Game ι S)
    (φ : (∀ j,S j) → ℝ) (hE : embed μ γ g=deltaAll μ φ) :
    ∀ i (s : ∀ j,S j) (a b : S i),
      γ i s*(g i (Function.update s i b)-g i (Function.update s i a))=
        φ (Function.update s i b)-φ (Function.update s i a) := by
  classical
  have edge (i : ι) (s t : ∀ j,S j) (hc : IsComparable i s t) :
      γ i s*(g i t-g i s)=φ t-φ s := by
    have hh := congrFun (congrFun hE s) t
    change (∑ j,delta μ j (coScale γ j (g j)) s t)=(∑ j,delta μ j φ s t) at hh
    rw [sum_on_comparable μ (fun j => coScale γ j (g j)) i s t hc,
      sum_on_comparable μ (fun _ => φ) i s t hc] at hh
    unfold delta coScale at hh
    rw [coScale_comparable γ hγ i s t hc] at hh
    have hW : 0 < W μ i s t := by
      rw [W,if_pos hc]
      exact one_div_pos.mpr (Real.sqrt_pos.mpr (except_positive μ hμ i s))
    have hg := mul_left_cancel₀ hW.ne' hh
    simpa only [← mul_sub] using hg
  intro i s a b
  by_cases hab : a=b
  · subst b;simp
  · have hc : IsComparable i (Function.update s i a) (Function.update s i b) := by
      constructor
      · simpa using hab
      · intro j hj;simp [Function.update_of_ne hj]
    simpa only [hγ.2 i s a] using edge i (Function.update s i a) (Function.update s i b) hc
lemma nonstrategic_kernel (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ j,S j) → ℝ) (hγ : IsCoMeasureVec γ) (g : Game ι S) :
    IsNonstrategic g ↔ embed μ γ g=0 := by
  constructor
  · intro hn
    have hφ : ∀ i (s : ∀ j,S j) (a b : S i),
        γ i s*(g i (Function.update s i b)-g i (Function.update s i a))=
          (fun _ => (0:ℝ)) (Function.update s i b)-(fun _ => (0:ℝ)) (Function.update s i a) := by
      intro i s a b
      rw [hn i s a,hn i s b]
      simp
    funext s t
    unfold embed
    apply Finset.sum_eq_zero
    intro i _
    rw [potential_gradients μ γ hγ g (fun _ => 0) hφ i]
    simp [delta]
  · intro he
    have hE : embed μ γ g=deltaAll μ (fun _ => 0) := by
      rw [he]
      funext s t
      simp [deltaAll,delta]
    have hp := potential_identity_of_embedding μ hμ γ hγ g (fun _ => 0) hE
    intro i s a
    have hh := hp i s (s i) a
    simp only [Function.update_eq_self,sub_self] at hh
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (hγ.1 i s).ne')
lemma potential_range (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ j,S j) → ℝ) (hγ : IsCoMeasureVec γ) (g : Game ι S) :
    IsPotential γ g ↔ ∃ φ : (∀ j,S j) → ℝ,embed μ γ g=deltaAll μ φ := by
  constructor
  · rintro ⟨φ,hφ⟩
    refine ⟨φ,?_⟩
    funext s t
    unfold embed deltaAll
    apply Finset.sum_congr rfl
    intro i _
    exact congrFun (congrFun (potential_gradients μ γ hγ g φ hφ i) s) t
  · rintro ⟨φ,hE⟩
    exact ⟨φ,potential_identity_of_embedding μ hμ γ hγ g φ hE⟩
lemma harmonic_divergence (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ j,S j) → ℝ) (hγ : IsCoMeasureVec γ) (g : Game ι S) :
    IsHarmonic μ γ g ↔ deltaStarAll μ (embed μ γ g)=0 := by
  have he (s : ∀ j,S j) : deltaStarAll μ (embed μ γ g) s=
      ∑ i,∑ a,μ i a*γ i s*(g i s-g i (Function.update s i a)) := by
    rw [star_embed]
    dsimp only
    apply Finset.sum_congr rfl
    intro i _
    rw [star_delta_sum μ hμ i (coScale γ i (g i)) s]
    apply Finset.sum_congr rfl
    intro a _
    unfold coScale
    rw [hγ.2 i s a]
    ring
  constructor
  · intro hg
    funext s
    change deltaStarAll μ (embed μ γ g) s=0
    rw [he]
    exact hg s
  · intro hg s
    rw [← he]
    simpa only [Pi.zero_apply] using congrFun hg s
end Queelius.GameFlowClasses
namespace DecompGames.Duplication
open Finset
 theorem _root_.flow_classes_solution {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ i, S i) → ℝ) (hγ : IsCoMeasureVec γ) :
    (∀ g : Game ι S, IsNonstrategic g ↔ embed μ γ g = 0) ∧
    (∀ g : Game ι S, IsPotential γ g ↔ ∃ φ : (∀ j, S j) → ℝ, embed μ γ g = deltaAll μ φ) ∧
    (∀ g : Game ι S, IsHarmonic μ γ g ↔ deltaStarAll μ (embed μ γ g) = 0) := by
  exact ⟨Queelius.GameFlowClasses.nonstrategic_kernel μ hμ γ hγ,
    Queelius.GameFlowClasses.potential_range μ hμ γ hγ,
    Queelius.GameFlowClasses.harmonic_divergence μ hμ γ hγ⟩
end DecompGames.Duplication

end

section
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
theorem _root_.extension_solution {ι : Type} [Fintype ι] [DecidableEq ι] {S S' : ι → Type}
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

end

open DecompGames.Duplication Finset
namespace Queelius.GameUnique
open Queelius.GameOrthogonal Queelius.GameAdjoint
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
  [∀ i,Fintype (S i)] [∀ i,DecidableEq (S i)]
lemma normalized_add (μ : ∀ i,S i → ℝ) (a b : Game ι S)
    (ha : IsNormalized μ a) (hb : IsNormalized μ b) : IsNormalized μ (a+b) := by
  intro i s
  simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib,ha i s,hb i s,add_zero]
lemma normalized_sub (μ : ∀ i,S i → ℝ) (a b : Game ι S)
    (ha : IsNormalized μ a) (hb : IsNormalized μ b) : IsNormalized μ (a-b) := by
  intro i s
  simp only [Pi.sub_apply,mul_sub,Finset.sum_sub_distrib,ha i s,hb i s,sub_self]
lemma potential_sub (γ : ι → (∀ i,S i) → ℝ) (a b : Game ι S)
    (ha : IsPotential γ a) (hb : IsPotential γ b) : IsPotential γ (a-b) := by
  obtain ⟨φ,hφ⟩ := ha
  obtain ⟨ψ,hψ⟩ := hb
  refine ⟨φ-ψ,?_⟩
  intro i s x y
  have h1 := hφ i s x y
  have h2 := hψ i s x y
  simp only [Pi.sub_apply]
  linear_combination h1-h2
lemma harmonic_sub (μ : ∀ i,S i → ℝ) (γ : ι → (∀ i,S i) → ℝ) (a b : Game ι S)
    (ha : IsHarmonic μ γ a) (hb : IsHarmonic μ γ b) : IsHarmonic μ γ (a-b) := by
  intro s
  have he : (∑ i,∑ t,μ i t*γ i s*((a-b) i s-(a-b) i (Function.update s i t)))=
      (∑ i,∑ t,μ i t*γ i s*(a i s-a i (Function.update s i t)))-
      (∑ i,∑ t,μ i t*γ i s*(b i s-b i (Function.update s i t))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    simp only [Pi.sub_apply]
    ring
  rw [he,ha s,hb s,sub_self]
lemma self_zero (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ i,S i) → ℝ) (hγ : IsCoMeasureVec γ) (g : Game ι S)
    (hg : ipGame μ γ g g=0) : g=0 := by
  have h0 (i : ι) : 0 ≤ ip0 μ (coScale γ i (g i)) (coScale γ i (g i)) := by
    apply Finset.sum_nonneg
    intro s _
    have hp := (product_positive μ hμ s).le
    dsimp [coScale]
    nlinarith [sq_nonneg (γ i s*g i s)]
  have hm (i : ι) : 0 ≤ mass μ i := Finset.sum_nonneg (fun a _ => (hμ i a).le)
  funext i s
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hm j) (h0 j))).mp hg i (Finset.mem_univ i)
  have hmass := mass_pos μ hμ i s
  have his : ip0 μ (coScale γ i (g i)) (coScale γ i (g i))=0 := (mul_eq_zero.mp hi).resolve_left hmass.ne'
  have hterms (t : ∀ j,S j) : 0 ≤ productMeasure μ t * coScale γ i (g i) t * coScale γ i (g i) t := by
    have hp := (product_positive μ hμ t).le
    nlinarith [sq_nonneg (coScale γ i (g i) t)]
  have ht := (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => hterms t)).mp his s (Finset.mem_univ s)
  have hp := product_positive μ hμ s
  have hc : coScale γ i (g i) s=0 := by
    rcases mul_eq_zero.mp ht with hz | hz
    · exact (mul_eq_zero.mp hz).resolve_left hp.ne'
    · exact hz
  change g i s=0
  exact (mul_eq_zero.mp hc).resolve_left (hγ.1 i s).ne'
lemma unique (μ : ∀ i,S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ i,S i) → ℝ) (hγ : IsCoMeasureVec γ)
    (g n p h n' p' h' : Game ι S) (h1 : IsDecomposition μ γ g n p h)
    (h2 : IsDecomposition μ γ g n' p' h') : n=n' ∧ p=p' ∧ h=h' := by
  obtain ⟨hn,⟨hpn,hpp⟩,⟨hhn,hhh⟩,hs⟩ := h1
  obtain ⟨hn',⟨hpn',hpp'⟩,⟨hhn',hhh'⟩,hs'⟩ := h2
  have hnval (n p h : Game ι S) (hn : IsNonstrategic n)
      (hp : IsNormalized μ p) (hh : IsNormalized μ h) (hs : g=n+p+h) : n=lamGame μ g := by
    rw [hs,(lamGame_linear μ).map_add,(lamGame_linear μ).map_add,
      average_fixed_game μ hμ n hn,(normalized_game_iff μ hμ p).mp hp,
      (normalized_game_iff μ hμ h).mp hh,add_zero,add_zero]
  have hnEq := (hnval n p h hn hpn hhn hs).trans (hnval n' p' h' hn' hpn' hhn' hs').symm
  have heq : p-p'=h'-h := by
    funext i s
    have h1 := congrFun (congrFun hs i) s
    have h2 := congrFun (congrFun hs' i) s
    rw [hnEq] at h1
    change p i s-p' i s=h' i s-h i s
    simp only [Pi.add_apply] at h1 h2
    linarith
  have hnorm := normalized_sub μ p p' hpn hpn'
  have hpot := potential_sub γ p p' hpp hpp'
  have hharm : IsHarmonic μ γ (p-p') := by rw [heq];exact harmonic_sub μ γ h' h hhh' hhh
  have hz := Queelius.GameTripleOrthogonal.potential_harmonic_orthogonal μ hμ γ hγ
    (p-p') (p-p') hnorm hpot hnorm hharm
  have hpEq : p=p' := sub_eq_zero.mp (self_zero μ hμ γ hγ (p-p') hz)
  have hhEq : h=h' := by
    funext i s
    have hv := congrFun (congrFun heq i) s
    rw [hpEq] at hv
    simpa using (sub_eq_zero.mp (show h' i s-h i s=0 by simpa using hv.symm)).symm
  exact ⟨hnEq,hpEq,hhEq⟩
end Queelius.GameUnique

namespace DecompGames.Duplication

open Finset

/-- Theorem 3.15, p. 19, for an extension along any collapsing map `π` (a single duplication is the
case of Definition 3.13): if `(n, p, h) = (g_{(μ,γ)-NS}, g_{(μ,γ)-P}, g_{(μ,γ)-H})` is the
`(μ, γ)`-decomposition of `g`, `μ̌` is an extension of `μ` and `γ̌ = Ť(γ)` is the extended
nonstrategic game of `γ`, then the `(μ̌, γ̌)`-decomposition of `ǧ = Ť(g)` is exactly
`(ň, p̌, ȟ)`: extensions and decompositions commute. -/
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {S S' : ι → Type}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, Fintype (S' i)] [∀ i, DecidableEq (S' i)]
    (μ : ∀ i, S i → ℝ) (hμ : IsMeasureVec μ)
    (γ : ι → (∀ i, S i) → ℝ) (hγ : IsCoMeasureVec γ)
    (π : ∀ i, S' i → S i) (μ' : ∀ i, S' i → ℝ) (hμ' : IsMeasureVec μ')
    (hext : IsMeasureExtension π μ μ')
    (g n p h : Game ι S) (hdec : IsDecomposition μ γ g n p h)
    (n' p' h' : Game ι S') :
    IsDecomposition μ' (extend π γ) (extend π g) n' p' h' ↔
      n' = extend π n ∧ p' = extend π p ∧ h' = extend π h := by
  have he := Queelius.GameExtension.decomposition π μ μ' hext γ g n p h hdec
  constructor
  · intro hd
    exact Queelius.GameUnique.unique μ' hμ' (extend π γ)
      (Queelius.GameExtension.coMeasure π γ hγ) (extend π g) n' p' h'
        (extend π n) (extend π p) (extend π h) hd he
  · rintro ⟨rfl,rfl,rfl⟩
    exact he

end DecompGames.Duplication
