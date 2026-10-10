-- Prove2me | solution 1 for FoundationsML.Regression.lipschitz_loss_rademacher_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-10T00:57:17.280712+00:00
-- url     : https://prove2.me/submissions/6753bd1b-2892-4dc5-9f7b-5af320b63f5a

/-
SPDX-License-Identifier: Apache-2.0
Complete proof of the canonical bounded Lipschitz-loss Rademacher contraction.
All custom proof bodies are included; only canonical definitions and Mathlib
are imported. The finite two-sign supremum argument and coordinate induction are reconstructed.
-/
import Mathlib
import Definitions.Def_FoundationsML_Regression_EmpiricalRademacherComplexity_v2
import Definitions.Def_FoundationsML_Regression_LossComposedFamily

/- Complete module: BoundedSup -/
section

namespace FoundationsML.Regression.Proof

lemma bddAbove_range_of_abs_bound {I : Type*} {f : I → ℝ}
    (hf : ∃ C, ∀ i, |f i| ≤ C) : BddAbove (Set.range f) := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨C, by rintro _ ⟨i, rfl⟩; exact (le_abs_self _).trans (hC i)⟩

lemma abs_bound_add {I : Type*} {f g : I → ℝ}
    (hf : ∃ C, ∀ i, |f i| ≤ C) (hg : ∃ C, ∀ i, |g i| ≤ C) :
    ∃ C, ∀ i, |f i + g i| ≤ C := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  exact ⟨A+B, fun i => (abs_add_le _ _).trans (add_le_add (hA i) (hB i))⟩

lemma abs_bound_neg {I : Type*} {f : I → ℝ}
    (hf : ∃ C, ∀ i, |f i| ≤ C) : ∃ C, ∀ i, |-f i| ≤ C := by
  simpa only [abs_neg] using hf

lemma abs_bound_mul {I : Type*} {f : I → ℝ}
    (hf : ∃ C, ∀ i, |f i| ≤ C) (r : ℝ) : ∃ C, ∀ i, |r * f i| ≤ C := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨|r| * C, fun i => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hC i) (abs_nonneg r)

lemma sup_add_sup_le_of_pairwise {I : Type*} [Nonempty I]
    (f g : I → ℝ) {C : ℝ} (h : ∀ i j, f i + g j ≤ C) :
    sSup (Set.range f) + sSup (Set.range g) ≤ C := by
  suffices hs : sSup (Set.range f) ≤ C - sSup (Set.range g) by linarith
  apply csSup_le (Set.range_nonempty f)
  rintro _ ⟨i, rfl⟩
  have hg : sSup (Set.range g) ≤ C - f i := by
    apply csSup_le (Set.range_nonempty g)
    rintro _ ⟨j, rfl⟩
    linarith [h i j]
  linarith

lemma range_sup_mul_nonneg {I : Type*} [Nonempty I] (f : I → ℝ)
    (hf : ∃ C, ∀ i, |f i| ≤ C) (r : ℝ) (hr : 0 ≤ r) :
    sSup (Set.range (fun i => r * f i)) = r * sSup (Set.range f) := by
  by_cases hr0 : r = 0
  · subst r
    simp
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hfb := bddAbove_range_of_abs_bound hf
  have hrfb := bddAbove_range_of_abs_bound (abs_bound_mul hf r)
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨i, rfl⟩
    exact mul_le_mul_of_nonneg_left (le_csSup hfb (Set.mem_range_self i)) hr
  · rw [mul_comm r]
    apply (le_div_iff₀ hrp).mp
    apply csSup_le (Set.range_nonempty f)
    rintro _ ⟨i, rfl⟩
    apply (le_div_iff₀ hrp).mpr
    simpa only [mul_comm] using le_csSup hrfb (Set.mem_range_self i)

end FoundationsML.Regression.Proof

end

/- Complete module: FiniteSigns -/
section

open scoped BigOperators
namespace FoundationsML.Regression.Proof

/-- The two equally weighted Rademacher values. -/
def radSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem abs_radSign (b : Bool) : |radSign b| = 1 := by cases b <;> norm_num [radSign]

/-- Unnormalized finite sign average, retaining an arbitrary offset. -/
noncomputable def signSup {I : Type*} {n : ℕ} (a : I → ℝ)
    (v : Fin n → I → ℝ) : ℝ :=
  ∑ σ : Fin n → Bool, sSup (Set.range (fun h => a h + ∑ i, radSign (σ i) * v i h))

theorem signSup_succ {I : Type*} {n : ℕ} (a : I → ℝ)
    (v : Fin (n+1) → I → ℝ) :
    signSup a v = signSup (fun h => a h + v 0 h) (fun i => v i.succ) +
      signSup (fun h => a h - v 0 h) (fun i => v i.succ) := by
  classical
  unfold signSup
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp,
    Fintype.sum_prod_type, Fintype.sum_bool]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro σ _ <;>
    congr 2 <;> funext h <;> simp [Fin.sum_univ_succ, Fin.consEquiv, radSign, sub_eq_add_neg,
      add_assoc]

theorem abs_bound_sign_sum {I : Type*} {n : ℕ} (v : Fin n → I → ℝ)
    (hv : ∀ j, ∃ B, ∀ i, |v j i| ≤ B) (σ : Fin n → Bool) :
    ∃ B, ∀ i, |∑ j, radSign (σ j)*v j i| ≤ B := by
  classical
  choose B hB using hv
  refine ⟨∑ j, B j, fun i => ?_⟩
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum (fun j _ => by simpa [abs_mul] using hB j i)

end FoundationsML.Regression.Proof

end

/- Complete module: TwoSupContraction -/
section

namespace FoundationsML.Regression.Proof

theorem two_sup_contraction {I : Type*} [Nonempty I]
    (a x y : I → ℝ) (μ : ℝ) (_hμ : 0 ≤ μ)
    (ha : ∃ A, ∀ i, |a i| ≤ A) (hx : ∃ B, ∀ i, |x i| ≤ B)
    (hxy : ∀ i j, y i - y j ≤ μ * |x i - x j|) :
    sSup (Set.range (fun i => a i + y i)) + sSup (Set.range (fun i => a i - y i)) ≤
      sSup (Set.range (fun i => a i + μ*x i)) +
        sSup (Set.range (fun i => a i - μ*x i)) := by
  have hbplus := bddAbove_range_of_abs_bound (abs_bound_add ha (abs_bound_mul hx μ))
  have hbminus : BddAbove (Set.range (fun i => a i - μ*x i)) := by
    simpa only [sub_eq_add_neg] using
      bddAbove_range_of_abs_bound (abs_bound_add ha (abs_bound_neg (abs_bound_mul hx μ)))
  apply sup_add_sup_le_of_pairwise
  intro i j
  have hij := hxy i j
  have hiP := le_csSup hbplus (Set.mem_range_self i)
  have hjP := le_csSup hbplus (Set.mem_range_self j)
  have hiN := le_csSup hbminus (Set.mem_range_self i)
  have hjN := le_csSup hbminus (Set.mem_range_self j)
  by_cases hle : x j ≤ x i
  · rw [abs_of_nonneg (sub_nonneg.mpr hle)] at hij
    linarith
  · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge hle))] at hij
    linarith

end FoundationsML.Regression.Proof

end

/- Complete module: CoordinateContraction -/
section

open scoped BigOperators
namespace FoundationsML.Regression.Proof

/-- Coordinatewise contraction with an arbitrary bounded offset. -/
theorem signSup_contraction {I : Type*} [Nonempty I] {n : ℕ}
    (a : I → ℝ) (x y : Fin n → I → ℝ) (μ : ℝ) (hμ : 0 ≤ μ)
    (ha : ∃ A, ∀ i, |a i| ≤ A)
    (hx : ∀ j, ∃ B, ∀ i, |x j i| ≤ B)
    (hy : ∀ j, ∃ B, ∀ i, |y j i| ≤ B)
    (hxy : ∀ j i k, y j i - y j k ≤ μ * |x j i - x j k|) :
    signSup a y ≤ signSup a (fun j i => μ*x j i) := by
  classical
  induction n generalizing a with
  | zero => simp [signSup]
  | succ n ih =>
    rw [signSup_succ, signSup_succ]
    have hhead :
        signSup (fun i => a i + y 0 i) (fun j => y j.succ) +
          signSup (fun i => a i - y 0 i) (fun j => y j.succ) ≤
        signSup (fun i => a i + μ*x 0 i) (fun j => y j.succ) +
          signSup (fun i => a i - μ*x 0 i) (fun j => y j.succ) := by
      unfold signSup
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro σ _
      have hh := two_sup_contraction
        (fun i => a i + ∑ j : Fin n, radSign (σ j)*y j.succ i)
        (x 0) (y 0) μ hμ
        (abs_bound_add ha (abs_bound_sign_sum _ (fun j => hy j.succ) σ))
        (hx 0) (hxy 0)
      simpa only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hh
    apply hhead.trans
    apply add_le_add
    · exact ih (fun i => a i + μ*x 0 i) (fun j => x j.succ) (fun j => y j.succ)
        (abs_bound_add ha (abs_bound_mul (hx 0) μ))
        (fun j => hx j.succ) (fun j => hy j.succ) (fun j => hxy j.succ)
    · exact ih (fun i => a i - μ*x 0 i) (fun j => x j.succ) (fun j => y j.succ)
        (by simpa only [sub_eq_add_neg] using
          abs_bound_add ha (abs_bound_neg (abs_bound_mul (hx 0) μ)))
        (fun j => hx j.succ) (fun j => hy j.succ) (fun j => hxy j.succ)

end FoundationsML.Regression.Proof

end

/- Complete module: EmpiricalSigns -/
section

open scoped BigOperators
namespace FoundationsML.Regression.Proof

theorem signSup_mul_nonneg {I : Type*} [Nonempty I] {n : ℕ}
    (x : Fin n → I → ℝ) (hx : ∀ j, ∃ B, ∀ i, |x j i| ≤ B)
    (μ : ℝ) (hμ : 0 ≤ μ) :
    signSup (fun _ => 0) (fun j i => μ*x j i) = μ*signSup (fun _ => 0) x := by
  classical
  unfold signSup
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [zero_add]
  have hh := range_sup_mul_nonneg (fun i => ∑ j, radSign (σ j)*x j i)
    (abs_bound_sign_sum x hx σ) μ hμ
  convert hh using 1
  congr 2
  funext i
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem empirical_signSup {Z : Type*} {m : ℕ} (G : Set (Z → ℝ))
    (S : Fin m → Z) :
    EmpiricalRademacherComplexity G S = (1/(2:ℝ)^m) *
      signSup (fun _ : G => 0) (fun j g => (1/(m:ℝ))*g.val (S j)) := by
  classical
  unfold EmpiricalRademacherComplexity signSup
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  ext z
  constructor
  · rintro ⟨g,hg,rfl⟩
    refine ⟨⟨g,hg⟩,?_⟩
    simp only [zero_add, Finset.mul_sum, radSign]
    congr 1
    funext j
    ring
  · rintro ⟨g,rfl⟩
    refine ⟨g.val,g.property,?_⟩
    simp only [zero_add, Finset.mul_sum, radSign]
    congr 1
    funext j
    ring

theorem empirical_loss_signSup {X : Type*} {m : ℕ} (L : ℝ → ℝ → ℝ)
    (H : Set (X → ℝ)) (S : Fin m → X × ℝ) :
    EmpiricalRademacherComplexity (LossComposedFamily L H) S = (1/(2:ℝ)^m) *
      signSup (fun _ : H => 0) (fun j h => (1/(m:ℝ))*L (h.val (S j).1) (S j).2) := by
  classical
  unfold EmpiricalRademacherComplexity signSup
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  ext z
  constructor
  · rintro ⟨g,⟨h,hh,rfl⟩,rfl⟩
    refine ⟨⟨h,hh⟩,?_⟩
    simp only [zero_add, Finset.mul_sum, radSign]
    congr 1
    funext j
    ring
  · rintro ⟨h,rfl⟩
    refine ⟨(fun p => L (h.val p.1) p.2),⟨h.val,h.property,rfl⟩,?_⟩
    simp only [zero_add, Finset.mul_sum, radSign]
    congr 1
    funext j
    ring

end FoundationsML.Regression.Proof

end

/- Complete module: ContractionRoot -/
section

namespace FoundationsML.Regression

/-- Proposition 11.2 (Rademacher complexity of µ-Lipschitz loss functions; Mohri,
Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 269,
PDF p. 286). Let `L` be a non-negative loss bounded by `M > 0` that is `µ`-Lipschitz in its
first argument, and `H` a (bounded, as Definition 3.1 requires) family of real-valued
functions. Then, for any sample `S`, the empirical Rademacher complexity of the loss-composed
family `G = {(x,y) ↦ L(h(x),y) : h ∈ H}` satisfies `R̂_S(G) ≤ µ R̂_S(H)`.

**Formalization Note.** Replaces `lipschitz_loss_rademacher_bound`, which used the retired
`EmpiricalRademacherComplexity` whose supremum `⨆ g ∈ G, …` on `ℝ` returns the junk value `0`
for an unbounded family, so an unbounded `H` had complexity `0` while the bounded `G` did not
(the disproof). The corrected `EmpiricalRademacherComplexity` (`_v2`, supremum over exactly
the family) is used, and Definition 3.1's standing assumption that `H` maps into a bounded
interval `[a,b]` is explicit (`hHb`); for unbounded `H` the book's right-hand side is `+∞`.
`hLlip` is Lipschitzness in the first argument only, with `y'` fixed. -/
theorem lipschitz_loss_rademacher_bound_v2
    {X : Type*} {m : ℕ}
    (L : ℝ → ℝ → ℝ) (M μ : ℝ) (hM : 0 < M) (hLnn : ∀ y y', 0 ≤ L y y')
    (hLb : ∀ y y', L y y' ≤ M) (hμ : 0 < μ)
    (hLlip : ∀ y' y1 y2, |L y1 y' - L y2 y'| ≤ μ * |y1 - y2|)
    (H : Set (X → ℝ)) (hHb : ∃ a b : ℝ, ∀ h ∈ H, ∀ x, h x ∈ Set.Icc a b)
    (S : Fin m → X × ℝ) :
    EmpiricalRademacherComplexity (LossComposedFamily L H) S ≤
      μ * EmpiricalRademacherComplexity H (fun i => (S i).1) := by
  classical
  have _positive_bound := hM
  rcases H.eq_empty_or_nonempty with hH | hH
  · subst H
    simp [EmpiricalRademacherComplexity, LossComposedFamily]
  let : Nonempty H := hH.to_subtype
  obtain ⟨a,b,hab⟩ := hHb
  have hx : ∀ j : Fin m, ∃ B, ∀ h : H, |(1/(m:ℝ))*h.val (S j).1| ≤ B := by
    intro j
    apply Proof.abs_bound_mul (r := (1/(m:ℝ)))
    refine ⟨|a|+|b|,fun h => ?_⟩
    obtain ⟨hal,hbu⟩ := hab h.val h.property (S j).1
    apply abs_le.mpr
    constructor <;> linarith [le_abs_self a, neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b]
  have hy : ∀ j : Fin m, ∃ B, ∀ h : H,
      |(1/(m:ℝ))*L (h.val (S j).1) (S j).2| ≤ B := by
    intro j
    apply Proof.abs_bound_mul (r := (1/(m:ℝ)))
    refine ⟨M,fun h => ?_⟩
    rw [abs_of_nonneg (hLnn _ _)]
    exact hLb _ _
  have hn : 0 ≤ 1/(m:ℝ) := by positivity
  have hh := Proof.signSup_contraction (fun _ : H => 0)
    (fun j h => (1/(m:ℝ))*h.val (S j).1)
    (fun j h => (1/(m:ℝ))*L (h.val (S j).1) (S j).2)
    μ hμ.le ⟨0,fun _ => by simp⟩ hx hy (by
      intro j h k
      calc
        _ = (1/(m:ℝ))*(L (h.val (S j).1) (S j).2-L (k.val (S j).1) (S j).2) := by ring
        _ ≤ (1/(m:ℝ))*(μ*|h.val (S j).1-k.val (S j).1|) :=
          mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hLlip _ _ _)) hn
        _ = _ := by rw [← mul_sub, abs_mul, abs_of_nonneg hn]; ring)
  rw [Proof.signSup_mul_nonneg _ hx μ hμ.le] at hh
  rw [Proof.empirical_loss_signSup, Proof.empirical_signSup]
  have hc : 0 ≤ 1/(2:ℝ)^m := by positivity
  calc
    _ ≤ (1/(2:ℝ)^m)*(μ*Proof.signSup (fun _ : H => 0)
      (fun j h => (1/(m:ℝ))*h.val (S j).1)) := mul_le_mul_of_nonneg_left hh hc
    _ = _ := by ring


end FoundationsML.Regression

theorem solution
    {X : Type*} {m : ℕ}
    (L : ℝ → ℝ → ℝ) (M μ : ℝ) (hM : 0 < M) (hLnn : ∀ y y', 0 ≤ L y y')
    (hLb : ∀ y y', L y y' ≤ M) (hμ : 0 < μ)
    (hLlip : ∀ y' y1 y2, |L y1 y' - L y2 y'| ≤ μ * |y1 - y2|)
    (H : Set (X → ℝ)) (hHb : ∃ a b : ℝ, ∀ h ∈ H, ∀ x, h x ∈ Set.Icc a b)
    (S : Fin m → X × ℝ) :
    FoundationsML.Regression.EmpiricalRademacherComplexity (FoundationsML.Regression.LossComposedFamily L H) S ≤
      μ * FoundationsML.Regression.EmpiricalRademacherComplexity H (fun i => (S i).1) := by
  exact FoundationsML.Regression.lipschitz_loss_rademacher_bound_v2 L M μ hM hLnn hLb hμ hLlip H hHb S

end
