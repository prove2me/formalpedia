-- Prove2me | solution 1 for CarbonDoubleCount.Leader.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T06:18:30.482125+00:00
-- url     : https://prove2.me/submissions/9bb7eaf8-c255-4f96-bbd1-1cb1ab318f0d

import Mathlib
import Definitions.Def_CarbonDoubleCount_Leader_Setting

set_option autoImplicit false

namespace P5Aux

/-- A function antitone on `[0,A]` and differentiable at a point of `[0,A]` has nonpositive
derivative there. -/
theorem deriv_nonpos_Icc {g : ℝ → ℝ} {A t0 : ℝ} (hA : 0 < A)
    (hg : AntitoneOn g (Set.Icc 0 A)) (ht : t0 ∈ Set.Icc 0 A) (hd : DifferentiableAt ℝ g t0) :
    deriv g t0 ≤ 0 := by
  rw [← hd.derivWithin (uniqueDiffOn_Icc hA t0 ht)]
  exact hg.derivWithin_nonpos

/-- If every partial derivative of `G` in firm `n`'s coordinates sums to a nonnegative number on
the box while `G` is antitone there, then `G` is constant along each coordinate line of firm `n`
inside the box. -/
theorem const_coord {ι : Type} [Fintype ι] [DecidableEq ι]
    {act : ι → Type} [∀ n, Fintype (act n)] [∀ n, DecidableEq (act n)]
    (A : ℝ) (hA : 0 < A) (G : ((n : ι) → act n → ℝ) → ℝ) (hG : Differentiable ℝ G)
    (hanti : AntitoneOn G (CarbonDoubleCount.Planner.effortBox A)) (n : ι)
    (hzero : ∀ e ∈ CarbonDoubleCount.Planner.effortBox A,
      ¬ (∑ j, CarbonDoubleCount.Leader.dEff G e n j < 0)) :
    ∀ e ∈ CarbonDoubleCount.Planner.effortBox A, ∀ j, ∀ t ∈ Set.Icc 0 A,
      G (Function.update e n (Function.update (e n) j t)) = G e := by
  let u : ((m : ι) → act m → ℝ) → act n → ℝ → ((m : ι) → act m → ℝ) :=
    fun e j t => Function.update e n (Function.update (e n) j t)
  have hu_diff : ∀ e j t, DifferentiableAt ℝ (u e j) t := by
    intro e j t
    exact (hasFDerivAt_update e (Function.update (e n) j t)).differentiableAt.comp t
      (hasDerivAt_update (e n) j t).differentiableAt
  have hu_box : ∀ e ∈ CarbonDoubleCount.Planner.effortBox A, ∀ j t, t ∈ Set.Icc 0 A →
      u e j t ∈ CarbonDoubleCount.Planner.effortBox A := by
    intro e he j t ht m k
    rcases eq_or_ne m n with rfl | hm
    · rcases eq_or_ne k j with rfl | hk
      · simpa [u] using ht
      · simpa [u, Function.update_of_ne hk] using he m k
    · simpa [u, Function.update_of_ne hm] using he m k
  have hu_mono : ∀ e j, Monotone (u e j) := by
    intro e j a b hab m k
    rcases eq_or_ne m n with rfl | hm
    · rcases eq_or_ne k j with rfl | hk
      · simpa [u] using hab
      · simp [u, Function.update_of_ne hk]
    · simp [u, Function.update_of_ne hm]
  have hu_self : ∀ e j, u e j (e n j) = e := by
    intro e j
    simp [u]
  have hu_u : ∀ e j t s, u (u e j t) j s = u e j s := by
    intro e j t s
    simp [u]
  have hu_at : ∀ e j t, u e j t n j = t := by
    intro e j t
    simp [u]
  -- sign of each partial derivative on the box
  have hneg : ∀ e ∈ CarbonDoubleCount.Planner.effortBox A, ∀ j,
      CarbonDoubleCount.Leader.dEff G e n j ≤ 0 := by
    intro e he j
    unfold CarbonDoubleCount.Leader.dEff
    apply deriv_nonpos_Icc hA _ (he n j) ((hG _).comp _ (hu_diff e j (e n j)))
    intro a ha b hb hab
    exact hanti (hu_box e he j a ha) (hu_box e he j b hb) (hu_mono e j hab)
  have hz : ∀ e ∈ CarbonDoubleCount.Planner.effortBox A, ∀ j,
      CarbonDoubleCount.Leader.dEff G e n j = 0 := by
    intro e he j
    have hle : ∑ j, CarbonDoubleCount.Leader.dEff G e n j ≤ 0 :=
      Finset.sum_nonpos (fun j _ => hneg e he j)
    have hge := not_lt.mp (hzero e he)
    have hsum : ∑ j, CarbonDoubleCount.Leader.dEff G e n j = 0 := le_antisymm hle hge
    exact (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => hneg e he j)).mp hsum j
      (Finset.mem_univ j)
  intro e he j t ht
  have hderiv : ∀ s ∈ Set.Icc 0 A, HasDerivAt (fun s => G (u e j s)) 0 s := by
    intro s hs
    have h1 : HasDerivAt (fun s => G (u e j s)) (deriv (fun s => G (u e j s)) s) s :=
      ((hG _).comp s (hu_diff e j s)).hasDerivAt
    have h2 : deriv (fun s => G (u e j s)) s = CarbonDoubleCount.Leader.dEff G (u e j s) n j := by
      unfold CarbonDoubleCount.Leader.dEff
      have : (fun r => G (Function.update (u e j s) n (Function.update (u e j s n) j r))) =
          (fun r => G (u e j r)) := by
        funext r
        exact congrArg G (hu_u e j s r)
      rw [this, hu_at]
    rw [h2, hz _ (hu_box e he j s hs)] at h1
    exact h1
  have hcont : ContinuousOn (fun s => G (u e j s)) (Set.Icc 0 A) :=
    fun s hs => (hderiv s hs).continuousAt.continuousWithinAt
  have hc := constant_of_has_deriv_right_zero hcont
    (fun s hs => (hderiv s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt)
  have h1 := hc t ht
  have h2 := hc (e n j) (he n j)
  show G (u e j t) = G e
  rw [h1, ← h2, hu_self]

/-- Under the same hypotheses, `G` does not change when firm `n` moves anywhere in its box. -/
theorem const_firm {ι : Type} [Fintype ι] [DecidableEq ι]
    {act : ι → Type} [∀ n, Fintype (act n)] [∀ n, DecidableEq (act n)]
    (A : ℝ) (hA : 0 < A) (G : ((n : ι) → act n → ℝ) → ℝ) (hG : Differentiable ℝ G)
    (hanti : AntitoneOn G (CarbonDoubleCount.Planner.effortBox A)) (n : ι)
    (hzero : ∀ e ∈ CarbonDoubleCount.Planner.effortBox A,
      ¬ (∑ j, CarbonDoubleCount.Leader.dEff G e n j < 0))
    (e : (m : ι) → act m → ℝ) (he : e ∈ CarbonDoubleCount.Planner.effortBox A)
    (x : act n → ℝ) (hx : x ∈ CarbonDoubleCount.Planner.firmBox A n) :
    G (Function.update e n x) = G e := by
  have hc := const_coord A hA G hG hanti n hzero
  let z : Finset (act n) → act n → ℝ := fun S j => if j ∈ S then x j else e n j
  have hzbox : ∀ S, Function.update e n (z S) ∈ CarbonDoubleCount.Planner.effortBox A := by
    intro S m k
    rcases eq_or_ne m n with rfl | hm
    · simp only [Function.update_self, z]
      split_ifs
      · exact hx k
      · exact he m k
    · simpa [Function.update_of_ne hm] using he m k
  have hind : ∀ S : Finset (act n), G (Function.update e n (z S)) = G e := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have : z ∅ = e n := by funext j; simp [z]
      rw [this, Function.update_eq_self]
    | insert a S haS ih =>
      have hzi : z (insert a S) = Function.update (z S) a (x a) := by
        funext j
        by_cases hj : j = a
        · subst hj; simp [z]
        · simp [z, Function.update_of_ne hj, hj]
      have key := hc (Function.update e n (z S)) (hzbox S) a (x a) (hx a)
      simp only [Function.update_self, Function.update_idem] at key
      rw [hzi, key, ih]
  have : z Finset.univ = x := by funext j; simp [z]
  rw [← this]
  exact hind Finset.univ

end P5Aux

open CarbonDoubleCount.Leader Finset in
theorem solution
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {act : ι → Type} [∀ n, Fintype (act n)] [∀ n, DecidableEq (act n)]
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (A p : ℝ) (hA : 0 < A) (hp : 0 ≤ p)
    (V : (n : ι) → (act n → ℝ) → ℝ) (f : ((n : ι) → act n → ℝ) → κ → ℝ)
    (hVdiff : ∀ n, Differentiable ℝ (V n))
    (hfdiff : ∀ i, Differentiable ℝ (fun e => f e i))
    (hVconc : ∀ n, ConcaveOn ℝ (CarbonDoubleCount.Planner.firmBox A n) (V n))
    (hVanti : ∀ n, AntitoneOn (V n) (CarbonDoubleCount.Planner.firmBox A n))
    (hfconv : ∀ i, ConvexOn ℝ (CarbonDoubleCount.Planner.effortBox A) (fun e => f e i))
    (hfanti : ∀ i, AntitoneOn (fun e => f e i) (CarbonDoubleCount.Planner.effortBox A))
    (hfnonneg : ∀ e ∈ CarbonDoubleCount.Planner.effortBox A, ∀ i, 0 ≤ f e i)
    (B : ι → κ → ℝ) (hB01 : ∀ n i, B n i = 0 ∨ B n i = 1)
    (hB : ∀ e ∈ CarbonDoubleCount.Planner.effortBox A, ∀ n i, (B n i = 1 ↔ ∑ j, dEff (fun e => f e i) e n j < 0))
    (L : ι) (πbar : ι → ℝ)
    (gE : (n : ι) → (act n → ℝ) → ℝ) (eE : (n : ι) → act n → ℝ)
    (hopt : IsOptimalPE A V f p L πbar gE eE)
    (hint : ∀ n j, 0 < eE n j ∧ eE n j < A) :
    PFFeasible A V f L πbar (rule12 V f p B πbar eE) eE ∧
      pfObjective V f p L (rule12 V f p B πbar eE) eE = peObjective V f p L gE eE ∧
      ∀ (g : ι → (κ → ℝ) → ℝ) (e : (n : ι) → act n → ℝ),
        PFFeasible A V f L πbar g e → pfObjective V f p L g e ≤ peObjective V f p L gE eE := by
  -- the first-best value at price `p`
  let W : ((n : ι) → act n → ℝ) → ℝ := fun e => ∑ m, V m (e m) - p * ∑ i, f e i
  set Pi : ℝ := ∑ n ∈ univ.erase L, πbar n with hPi
  have hsplitL : ∀ e : (n : ι) → act n → ℝ,
      ∑ m, V m (e m) = V L (e L) + ∑ m ∈ univ.erase L, V m (e m) := by
    intro e
    exact (Finset.add_sum_erase _ (fun m => V m (e m)) (Finset.mem_univ L)).symm
  have hbox : eE ∈ CarbonDoubleCount.Planner.effortBox A := hopt.1.1
  have hpartE : ∀ n, n ≠ L → gE n (eE n) ≤ V n (eE n) - πbar n := by
    intro n hn
    have := hopt.1.2.1 n hn
    linarith
  -- objective of any feasible pair is at most `W e - Pi`
  have hPEle : peObjective V f p L gE eE ≤ W eE - Pi := by
    have hs : ∑ n ∈ univ.erase L, gE n (eE n) ≤ ∑ n ∈ univ.erase L, (V n (eE n) - πbar n) :=
      Finset.sum_le_sum (fun n hn => hpartE n (Finset.ne_of_mem_erase hn))
    rw [Finset.sum_sub_distrib] at hs
    have := hsplitL eE
    simp only [peObjective, W]
    linarith
  -- every effort profile in the box is achievable in `P_E`
  have hPEge : ∀ e' ∈ CarbonDoubleCount.Planner.effortBox A,
      W e' - Pi ≤ peObjective V f p L gE eE := by
    intro e' he'
    let g' : (n : ι) → (act n → ℝ) → ℝ := fun n x => V n x - πbar n
    have hfeas : PEFeasible A V L πbar g' e' := by
      refine ⟨he', fun n _ => ?_, fun n _ x _ => ?_⟩
      · simp [g']
      · simp [g']
    have h := hopt.2 g' e' hfeas
    have hval : peObjective V f p L g' e' = W e' - Pi := by
      simp only [peObjective, W, g']
      rw [Finset.sum_sub_distrib, hsplitL e']
      ring
    linarith
  have hFB : ∀ e' ∈ CarbonDoubleCount.Planner.effortBox A, W e' ≤ W eE := by
    intro e' he'
    have := hPEge e' he'
    linarith
  have hPEval : peObjective V f p L gE eE = W eE - Pi :=
    le_antisymm hPEle (hPEge eE hbox)
  -- rule (12) evaluated at the target emissions
  have hrule_at : ∀ n, rule12 V f p B πbar eE n (f eE) = V n (eE n) - πbar n := by
    intro n
    simp only [rule12]
    ring
  refine ⟨⟨hbox, fun n _ => ?_, fun n hn x hx => ?_⟩, ?_, ?_⟩
  · rw [hrule_at]
    linarith
  · -- incentive compatibility of rule (12)
    have hxbox : Function.update eE n x ∈ CarbonDoubleCount.Planner.effortBox A := by
      intro m k
      rcases eq_or_ne m n with rfl | hm
      · simpa using hx k
      · simpa [Function.update_of_ne hm] using hbox m k
    have hsplitn : ∀ y : act n → ℝ,
        ∑ m, V m (Function.update eE n y m) = V n y + ∑ m ∈ univ.erase n, V m (eE m) := by
      intro y
      rw [← Finset.add_sum_erase _ (fun m => V m (Function.update eE n y m)) (Finset.mem_univ n)]
      simp only [Function.update_self]
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hm)]
    have hconst : ∀ i, B n i = 0 → f (Function.update eE n x) i = f eE i := by
      intro i hi
      refine P5Aux.const_firm A hA (fun e => f e i) (hfdiff i) (hfanti i) n ?_ eE hbox x hx
      intro e he hlt
      have := (hB e he n i).mpr hlt
      rw [hi] at this
      norm_num at this
    have hkey : ∀ i, B n i * f (Function.update eE n x) i =
        f (Function.update eE n x) i - f eE i + B n i * f eE i := by
      intro i
      rcases hB01 n i with h | h
      · rw [h, hconst i h]; ring
      · rw [h]; ring
    have hsumB : ∑ i, B n i * f (Function.update eE n x) i =
        ∑ i, f (Function.update eE n x) i - ∑ i, f eE i + ∑ i, B n i * f eE i := by
      rw [Finset.sum_congr rfl (fun i _ => hkey i), Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
    have h1 := hFB _ hxbox
    have h2 := hsplitn x
    have h3 := hsplitn (eE n)
    rw [Function.update_eq_self] at h3
    simp only [W] at h1
    rw [h2, h3] at h1
    rw [hrule_at]
    simp only [rule12]
    rw [hsumB]
    have e1 : p * (∑ i, f (Function.update eE n x) i - ∑ i, f eE i + ∑ i, B n i * f eE i) =
        p * ∑ i, f (Function.update eE n x) i - p * ∑ i, f eE i + p * ∑ i, B n i * f eE i := by
      ring
    rw [e1]
    linarith
  · -- the objective value
    rw [hPEval]
    simp only [pfObjective, W]
    rw [Finset.sum_congr rfl (fun n _ => hrule_at n), Finset.sum_sub_distrib, hsplitL eE]
    ring
  · -- optimality
    intro g e he
    have hs : ∑ n ∈ univ.erase L, g n (f e) ≤ ∑ n ∈ univ.erase L, (V n (e n) - πbar n) :=
      Finset.sum_le_sum (fun n hn => by
        have := he.2.1 n (Finset.ne_of_mem_erase hn)
        linarith)
    rw [Finset.sum_sub_distrib] at hs
    have h1 := hFB e he.1
    have h2 := hsplitL e
    rw [hPEval]
    simp only [pfObjective]
    simp only [W] at h1 ⊢
    linarith
