-- Prove2me | solution 1 for FiniteFields.dwork_rationality_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T07:04:26.29337+00:00
-- url     : https://prove2.me/submissions/a609a7ec-d91a-42f5-be3e-6063be29c9d8

import Mathlib
import Definitions.Def_FiniteFields_Dwork_Devissage
import Theorems.Thm_FiniteFields_Dwork_affineHypersurfaceZeta_archimedeanGrowth
import Theorems.Thm_FiniteFields_Dwork_coefficientField_valuation_p
import Theorems.Thm_FiniteFields_Dwork_borelDwork_rationalityCriterion
import Theorems.Thm_FiniteFields_Dwork_dworkToricZeta_isPadicMeromorphic
import Theorems.Thm_FiniteFields_Dwork_zetaSeriesOf_sum
section
noncomputable section
namespace FiniteFields
variable (k : Type*) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
theorem natCard_extension (n : ℕ) :
    Nat.card (Extension k p n) = Nat.card k ^ (n + 1) := by
  exact FiniteField.natCard_extension k p (n + 1)
theorem natCard_affinePoints (d n : ℕ) :
    Nat.card (AffinePoints k p d n) =
      (Nat.card k ^ (n + 1)) ^ d := by
  rw [Nat.card_fun, Nat.card_fin, natCard_extension]
end FiniteFields
end
end
section
noncomputable section
namespace FiniteFields
open PowerSeries
@[simp]
theorem coeff_countingSeries (N : ℕ → ℕ) (n : ℕ) :
    PowerSeries.coeff n (countingSeries N) = (N n : ℚ) := by
  simp [countingSeries]
theorem IsZetaSeries.unique {N : ℕ → ℕ} {Z W : ℚ⟦X⟧}
    (hZ : IsZetaSeries N Z) (hW : IsZetaSeries N W) : Z = W := by
  exact PowerSeries.eq_of_derivative_eq_mul
    (by simpa only [mul_comm] using hZ.2) (by simpa only [mul_comm] using hW.2)
    (hZ.1.trans hW.1.symm)
end FiniteFields
end
end
section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {d : ℕ}
theorem affineHypersurfacePointCount_eq_tupleCount (f : MvPolynomial (Fin d) k) (n : ℕ) :
    affineHypersurfacePointCount k p f n = Nat.card (AffineHypersurfaceTuples k p f n) :=
  Nat.card_congr (affineHypersurfaceExtensionPointEquiv k p f n)
@[simp]
theorem constantCoeff_zetaLog (N : ℕ → ℕ) :
    PowerSeries.constantCoeff (zetaLog N) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, zetaLog, PowerSeries.coeff_mk]
  simp
theorem derivative_zetaLog (N : ℕ → ℕ) :
    PowerSeries.derivative ℚ (zetaLog N) = countingSeries N := by
  ext n
  rw [PowerSeries.coeff_derivative, zetaLog, PowerSeries.coeff_mk, coeff_countingSeries]
  have hne : (n : ℚ) + 1 ≠ 0 := by positivity
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
  field_simp
  push_cast
  ring
theorem constantCoeff_zetaSeriesOf (N : ℕ → ℕ) :
    PowerSeries.constantCoeff (zetaSeriesOf N) = 1 := by
  rw [zetaSeriesOf, ← PowerSeries.coeff_zero_eq_constantCoeff,
    PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero'
      (constantCoeff_zetaLog N)), finsum_eq_single _ 0]
  · simp
  · intro e he
    simp [he, constantCoeff_zetaLog]
theorem derivative_zetaSeriesOf (N : ℕ → ℕ) :
    PowerSeries.derivative ℚ (zetaSeriesOf N) = countingSeries N * zetaSeriesOf N := by
  rw [zetaSeriesOf, PowerSeries.derivative_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_zetaLog N)),
    PowerSeries.derivative_exp, derivative_zetaLog, mul_comm]
theorem zetaSeriesOf_isZetaSeries (N : ℕ → ℕ) : IsZetaSeries N (zetaSeriesOf N) :=
  ⟨constantCoeff_zetaSeriesOf N, derivative_zetaSeriesOf N⟩
theorem affineHypersurfaceZetaSeries_isZetaSeries (f : MvPolynomial (Fin d) k) :
    IsZetaSeries (affineHypersurfacePointCount k p f) (affineHypersurfaceZetaSeries k p f) :=
  zetaSeriesOf_isZetaSeries _
theorem coeff_succ_of_isZetaSeries {N : ℕ → ℕ} {Z : ℚ⟦X⟧} (hZ : IsZetaSeries N Z) (m : ℕ) :
    PowerSeries.coeff (m + 1) Z * ((m : ℚ) + 1)
      = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m, (N ij.1 : ℚ) * PowerSeries.coeff ij.2 Z := by
  have h := congrArg (PowerSeries.coeff m) hZ.2
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at h
  rw [h]
  exact Finset.sum_congr rfl fun ij _ => by rw [coeff_countingSeries]
end FiniteFields.Dwork
end
end
section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {d : ℕ}
section Orbits
variable {α : Type*} [DecidableEq α] (φ : α → α) {e : ℕ}
omit [DecidableEq α] in
private theorem iterate_mem_of_closed {X : Finset α} (hclosed : ∀ x ∈ X, φ x ∈ X)
    {x : α} (hx : x ∈ X) : ∀ j, φ^[j] x ∈ X := by
  intro j
  induction j with
  | zero => simpa using hx
  | succ j ih => rw [Function.iterate_succ_apply']; exact hclosed _ ih
omit [DecidableEq α] in
private theorem injOn_of_period {X : Finset α} (he : 0 < e)
    (hper : ∀ x ∈ X, φ^[e] x = x) {a b : α} (ha : a ∈ X) (hb : b ∈ X) (hab : φ a = φ b) :
    a = b := by
  have hra : φ^[e - 1] (φ a) = a := by
    rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel he]
    exact hper a ha
  have hrb : φ^[e - 1] (φ b) = b := by
    rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel he]
    exact hper b hb
  rw [← hra, hab, hrb]
theorem dvd_card_of_forall_exact_period (he : 0 < e) :
    ∀ X : Finset α, (∀ x ∈ X, φ x ∈ X) → (∀ x ∈ X, φ^[e] x = x) →
      (∀ x ∈ X, ∀ j, 0 < j → j < e → φ^[j] x ≠ x) → e ∣ X.card := by
  intro X
  induction X using Finset.strongInduction with
  | _ X ih =>
      intro hclosed hper hmin
      rcases X.eq_empty_or_nonempty with rfl | hne
      · simp
      obtain ⟨x, hx⟩ := hne
      set O : Finset α := (Finset.range e).image (fun j => φ^[j] x) with hOdef
      have hOsub : O ⊆ X := by
        intro y hy
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
        exact iterate_mem_of_closed φ hclosed hx j
      have hinj : Set.InjOn (fun j => φ^[j] x) (Finset.range e : Finset ℕ) := by
        intro i hi j hj hij
        have hij' : φ^[i] x = φ^[j] x := hij
        by_contra hne'
        rw [Finset.mem_coe, Finset.mem_range] at hi hj
        rcases Nat.lt_or_ge i j with hlt | hge
        · refine hmin x hx (e - j + i) (by omega) (by omega) ?_
          have : φ^[e - j] (φ^[i] x) = φ^[e - j] (φ^[j] x) := by rw [hij']
          rwa [← Function.iterate_add_apply, ← Function.iterate_add_apply,
            show e - j + j = e from by omega, hper x hx] at this
        · have hlt' : j < i := by omega
          refine hmin x hx (e - i + j) (by omega) (by omega) ?_
          have : φ^[e - i] (φ^[j] x) = φ^[e - i] (φ^[i] x) := by rw [hij']
          rwa [← Function.iterate_add_apply, ← Function.iterate_add_apply,
            show e - i + i = e from by omega, hper x hx] at this
      have hOcard : O.card = e := by
        rw [hOdef, Finset.card_image_of_injOn hinj, Finset.card_range]
      have hclosed' : ∀ y ∈ X \ O, φ y ∈ X \ O := by
        intro y hy
        rw [Finset.mem_sdiff] at hy ⊢
        refine ⟨hclosed y hy.1, ?_⟩
        intro hmem
        obtain ⟨j, hj, hjy⟩ := Finset.mem_image.mp hmem
        rw [Finset.mem_range] at hj
        apply hy.2
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · have : y = φ^[e - 1] x := by
            have h1 : φ^[e - 1] (φ y) = y := by
              rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel he]
              exact hper y hy.1
            rw [← h1]
            simp only [Function.iterate_zero, id_eq] at hjy
            rw [← hjy]
          rw [this, hOdef]
          exact Finset.mem_image.mpr ⟨e - 1, Finset.mem_range.mpr (by omega), rfl⟩
        · have hy' : y = φ^[j - 1] x := by
            refine injOn_of_period φ he hper hy.1 (iterate_mem_of_closed φ hclosed hx (j - 1)) ?_
            have hstep : φ^[(j - 1) + 1] x = φ (φ^[j - 1] x) :=
              Function.iterate_succ_apply' φ (j - 1) x
            rw [← hjy, ← hstep, Nat.sub_add_cancel hjpos]
          rw [hy', hOdef]
          exact Finset.mem_image.mpr ⟨j - 1, Finset.mem_range.mpr (by omega), rfl⟩
      have hssub : X \ O ⊂ X := by
        refine Finset.sdiff_ssubset hOsub ?_
        exact ⟨x, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr he, by simp⟩⟩
      have hrec := ih (X \ O) hssub hclosed'
        (fun y hy => hper y (Finset.mem_sdiff.mp hy).1)
        (fun y hy => hmin y (Finset.mem_sdiff.mp hy).1)
      have hcard : X.card = (X \ O).card + e := by
        have hinter : O ∩ X = O := Finset.inter_eq_left.mpr hOsub
        rw [Finset.card_sdiff, hinter, hOcard]
        have hle : e ≤ X.card := hOcard ▸ Finset.card_le_card hOsub
        omega
      rw [hcard]
      exact Nat.dvd_add hrec dvd_rfl
end Orbits
variable (f : MvPolynomial (Fin d) k)
theorem solutionFrobenius_iterate_extensionDegree (n : ℕ)
    (x : AffineHypersurfaceTuples k p f n) :
    (solutionFrobenius k p f n)^[n + 1] x = x := by
  apply Subtype.ext
  funext i
  rw [solutionFrobenius_iterate_coord]
  exact pow_natCard_pow_self k p n (x.1 i)
private theorem mem_periodicPts_solution (n : ℕ) (x : AffineHypersurfaceTuples k p f n) :
    x ∈ Function.periodicPts (solutionFrobenius k p f n) :=
  ⟨n + 1, Nat.succ_pos n, solutionFrobenius_iterate_extensionDegree k p f n x⟩
private theorem minimalPeriod_dvd_succ (n : ℕ) (x : AffineHypersurfaceTuples k p f n) :
    Function.minimalPeriod (solutionFrobenius k p f n) x ∣ n + 1 :=
  Function.IsPeriodicPt.minimalPeriod_dvd
    (solutionFrobenius_iterate_extensionDegree k p f n x)
theorem pointCount_eq_sum_exactPeriod (n : ℕ) :
    affineHypersurfacePointCount k p f n
      = ∑ e ∈ (n + 1).divisors, (exactPeriodSolutions k p f n e).card := by
  classical
  rw [affineHypersurfacePointCount_eq_tupleCount, Nat.card_eq_fintype_card,
    ← Finset.card_univ]
  exact Finset.card_eq_sum_card_fiberwise fun x _ =>
    Nat.mem_divisors.mpr ⟨minimalPeriod_dvd_succ k p f n x, Nat.succ_ne_zero n⟩
theorem dvd_card_exactPeriodSolutions (n e : ℕ) (he : 0 < e) :
    e ∣ (exactPeriodSolutions k p f n e).card := by
  classical
  refine dvd_card_of_forall_exact_period (solutionFrobenius k p f n) he _ ?_ ?_ ?_
  · intro x hx
    rw [exactPeriodSolutions, Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_univ _,
      (Function.minimalPeriod_apply (mem_periodicPts_solution k p f n x)).trans hx.2⟩
  · intro x hx
    rw [exactPeriodSolutions, Finset.mem_filter] at hx
    have := Function.isPeriodicPt_minimalPeriod (solutionFrobenius k p f n) x
    rwa [hx.2] at this
  · intro x hx j hj hje
    rw [exactPeriodSolutions, Finset.mem_filter] at hx
    exact Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod hj.ne' (by rw [hx.2]; exact hje)
private theorem towerSolution_comm {a b : ℕ} (h : (a + 1) ∣ (b + 1))
    (y : AffineHypersurfaceTuples k p f a) :
    towerSolution k p f h (solutionFrobenius k p f a y)
      = solutionFrobenius k p f b (towerSolution k p f h y) := by
  apply Subtype.ext
  funext i
  show towerHom k p h ((arithmeticFrobenius k p a) (y.1 i))
    = (arithmeticFrobenius k p b) (towerHom k p h (y.1 i))
  rw [arithmeticFrobenius_apply, arithmeticFrobenius_apply, map_pow]
private theorem towerSolution_iterate {a b : ℕ} (h : (a + 1) ∣ (b + 1)) (j : ℕ)
    (y : AffineHypersurfaceTuples k p f a) :
    (solutionFrobenius k p f b)^[j] (towerSolution k p f h y)
      = towerSolution k p f h ((solutionFrobenius k p f a)^[j] y) := by
  induction j generalizing y with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih, towerSolution_comm]
private theorem minimalPeriod_towerSolution {a b : ℕ} (h : (a + 1) ∣ (b + 1))
    (y : AffineHypersurfaceTuples k p f a) :
    Function.minimalPeriod (solutionFrobenius k p f b) (towerSolution k p f h y)
      = Function.minimalPeriod (solutionFrobenius k p f a) y := by
  have hiff : ∀ j, (solutionFrobenius k p f b)^[j] (towerSolution k p f h y)
      = towerSolution k p f h y ↔ (solutionFrobenius k p f a)^[j] y = y := by
    intro j
    rw [towerSolution_iterate]
    exact ⟨fun hj => towerSolution_injective k p f h hj, fun hj => by rw [hj]⟩
  refine Nat.dvd_antisymm ?_ ?_
  · refine Function.IsPeriodicPt.minimalPeriod_dvd ?_
    show (solutionFrobenius k p f b)^[_] (towerSolution k p f h y) = _
    exact (hiff _).mpr (Function.isPeriodicPt_minimalPeriod _ y)
  · refine Function.IsPeriodicPt.minimalPeriod_dvd ?_
    show (solutionFrobenius k p f a)^[_] y = _
    exact (hiff _).mp (Function.isPeriodicPt_minimalPeriod _ (towerSolution k p f h y))
theorem card_exactPeriodSolutions_eq {a b : ℕ} (h : (a + 1) ∣ (b + 1)) :
    (exactPeriodSolutions k p f b (a + 1)).card
      = (exactPeriodSolutions k p f a (a + 1)).card := by
  classical
  refine (Finset.card_bij (fun y _ => towerSolution k p f h y) ?_ ?_ ?_).symm
  · intro y hy
    rw [exactPeriodSolutions, Finset.mem_filter] at hy ⊢
    exact ⟨Finset.mem_univ _, (minimalPeriod_towerSolution k p f h y).trans hy.2⟩
  · intro y _ z _ hyz
    exact towerSolution_injective k p f h hyz
  · intro x hx
    rw [exactPeriodSolutions, Finset.mem_filter] at hx
    have hfix : (solutionFrobenius k p f b)^[a + 1] x = x := by
      have := Function.isPeriodicPt_minimalPeriod (solutionFrobenius k p f b) x
      rwa [hx.2] at this
    obtain ⟨y, hy⟩ : ∃ y, towerSolution k p f h y = x := by
      refine ⟨(fixedSolutionEquiv k p f h).symm ⟨x, hfix⟩, ?_⟩
      have := (fixedSolutionEquiv k p f h).apply_symm_apply ⟨x, hfix⟩
      exact congrArg Subtype.val this
    refine ⟨y, ?_, hy⟩
    rw [exactPeriodSolutions, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← minimalPeriod_towerSolution k p f h y, hy, hx.2]
theorem pointCount_eq_sum_orbitCount (n : ℕ) :
    affineHypersurfacePointCount k p f n
      = ∑ e ∈ (n + 1).divisors, e * orbitCount k p f e := by
  rw [pointCount_eq_sum_exactPeriod]
  refine Finset.sum_congr rfl fun e he => ?_
  obtain ⟨hdvd, _⟩ := Nat.mem_divisors.mp he
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos hdvd (Nat.succ_pos n)
  have hsucc : (e - 1) + 1 = e := Nat.succ_pred_eq_of_pos hepos
  have hstep : (exactPeriodSolutions k p f n e).card
      = (exactPeriodSolutions k p f (e - 1) e).card := by
    have := card_exactPeriodSolutions_eq k p f (a := e - 1) (b := n) (by rw [hsucc]; exact hdvd)
    rwa [hsucc] at this
  rw [hstep, orbitCount, Nat.mul_div_cancel']
  exact dvd_card_exactPeriodSolutions k p f (e - 1) e hepos
end FiniteFields.Dwork
end
end
section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {d : ℕ}
variable (f : MvPolynomial (Fin d) k)
theorem coeff_geomFactor (R : Type*) [CommRing R] (e j : ℕ) :
    PowerSeries.coeff j (geomFactor R e) = if e ∣ j then 1 else 0 :=
  PowerSeries.coeff_mk _ _
theorem map_geomFactor (e : ℕ) :
    PowerSeries.map (Int.castRingHom ℚ) (geomFactor ℤ e) = geomFactor ℚ e := by
  ext j
  rw [PowerSeries.coeff_map, coeff_geomFactor, coeff_geomFactor]
  split <;> simp
omit [Finite k] [Fact p.Prime] [CharP k p] in
theorem one_sub_mul_geomFactor (e : ℕ) (he : 0 < e) :
    (1 - PowerSeries.X ^ e) * geomFactor ℚ e = 1 := by
  ext m
  rw [sub_mul, one_mul, map_sub, coeff_geomFactor, PowerSeries.coeff_X_pow_mul']
  by_cases hm : e ≤ m
  · rw [if_pos hm, coeff_geomFactor]
    have hiff : e ∣ m ↔ e ∣ m - e := by
      constructor
      · intro hd; exact Nat.dvd_sub hd dvd_rfl
      · intro hd
        have := Nat.dvd_add hd (dvd_refl e)
        rwa [Nat.sub_add_cancel hm] at this
    by_cases hd : e ∣ m
    · rw [if_pos hd, if_pos (hiff.mp hd), sub_self]
      rw [PowerSeries.coeff_one, if_neg (by omega)]
    · rw [if_neg hd, if_neg (fun hc => hd (hiff.mpr hc)), sub_zero]
      rw [PowerSeries.coeff_one, if_neg (by omega)]
  · rw [if_neg hm, sub_zero, PowerSeries.coeff_one]
    by_cases hm0 : m = 0
    · subst hm0
      rw [if_pos (dvd_zero e), if_pos rfl]
    · rw [if_neg hm0, if_neg (fun hc => hm (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hc))]
omit [Finite k] [Fact p.Prime] [CharP k p] in
theorem derivative_geomFactor (e : ℕ) (he : 0 < e) :
    PowerSeries.derivative ℚ (geomFactor ℚ e)
      = (e : ℚ⟦X⟧) * PowerSeries.X ^ (e - 1) * (geomFactor ℚ e * geomFactor ℚ e) := by
  have hinv : (1 - PowerSeries.X ^ e) * geomFactor ℚ e = 1 := one_sub_mul_geomFactor e he
  have hdX : PowerSeries.derivative ℚ ((1 : ℚ⟦X⟧) - PowerSeries.X ^ e)
      = -((e : ℚ⟦X⟧) * PowerSeries.X ^ (e - 1)) := by
    rw [map_sub, Derivation.map_one_eq_zero, PowerSeries.derivative_pow,
      PowerSeries.derivative_X, mul_one, zero_sub]
  have hd := congrArg (PowerSeries.derivative ℚ) hinv
  rw [Derivation.leibniz, Derivation.map_one_eq_zero, hdX] at hd
  simp only [smul_eq_mul] at hd
  have hkey : (1 - PowerSeries.X ^ e) * PowerSeries.derivative ℚ (geomFactor ℚ e)
      = (e : ℚ⟦X⟧) * PowerSeries.X ^ (e - 1) * geomFactor ℚ e := by
    linear_combination hd
  calc PowerSeries.derivative ℚ (geomFactor ℚ e)
      = ((1 - PowerSeries.X ^ e) * geomFactor ℚ e)
          * PowerSeries.derivative ℚ (geomFactor ℚ e) := by rw [hinv, one_mul]
    _ = ((1 - PowerSeries.X ^ e) * PowerSeries.derivative ℚ (geomFactor ℚ e))
          * geomFactor ℚ e := by ring
    _ = (e : ℚ⟦X⟧) * PowerSeries.X ^ (e - 1) * (geomFactor ℚ e * geomFactor ℚ e) := by
        rw [hkey]; ring
omit [Finite k] [Fact p.Prime] [CharP k p] in
private theorem derivative_geomFactor_pow (e c : ℕ) (he : 0 < e) :
    PowerSeries.derivative ℚ ((geomFactor ℚ e) ^ c)
      = (c : ℚ⟦X⟧) * (e : ℚ⟦X⟧) * PowerSeries.X ^ (e - 1) * geomFactor ℚ e
          * (geomFactor ℚ e) ^ c := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [pow_succ, Derivation.leibniz, ih, derivative_geomFactor e he]
      simp only [smul_eq_mul]
      push_cast
      ring
private theorem derivative_prod_geom (s : Finset ℕ) (hs : ∀ e ∈ s, 0 < e) :
    PowerSeries.derivative ℚ (∏ e ∈ s, (geomFactor ℚ e) ^ (orbitCount k p f e))
      = (∑ e ∈ s, (orbitCount k p f e : ℚ⟦X⟧) * (e : ℚ⟦X⟧) * PowerSeries.X ^ (e - 1)
            * geomFactor ℚ e)
        * ∏ e ∈ s, (geomFactor ℚ e) ^ (orbitCount k p f e) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      have hpos : 0 < a := hs a (Finset.mem_insert_self a t)
      have iht := ih (fun e he => hs e (Finset.mem_insert_of_mem he))
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Derivation.leibniz, iht,
        derivative_geomFactor_pow a _ hpos]
      simp only [smul_eq_mul]
      ring
theorem derivative_eulerPartialQ (M : ℕ) :
    PowerSeries.derivative ℚ (eulerPartialQ k p f M)
      = eulerLogDeriv k p f M * eulerPartialQ k p f M :=
  derivative_prod_geom k p f _ fun _ he => (Finset.mem_Icc.mp he).1
theorem constantCoeff_eulerPartialQ (M : ℕ) :
    PowerSeries.constantCoeff (eulerPartialQ k p f M) = 1 := by
  rw [eulerPartialQ, map_prod]
  refine Finset.prod_eq_one fun e _ => ?_
  rw [map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_geomFactor,
    if_pos (dvd_zero e), one_pow]
theorem coeff_eulerLogDeriv (M j : ℕ) (hj : j + 1 ≤ M) :
    PowerSeries.coeff j (eulerLogDeriv k p f M)
      = (affineHypersurfacePointCount k p f j : ℚ) := by
  classical
  have hterm : ∀ e ∈ Finset.Icc 1 M,
      PowerSeries.coeff j ((orbitCount k p f e : ℚ⟦X⟧) * (e : ℚ⟦X⟧)
          * PowerSeries.X ^ (e - 1) * geomFactor ℚ e)
        = if e ∈ (j + 1).divisors then ((e * orbitCount k p f e : ℕ) : ℚ) else 0 := by
    intro e he
    obtain ⟨he1, _⟩ := Finset.mem_Icc.mp he
    have hrw : (orbitCount k p f e : ℚ⟦X⟧) * (e : ℚ⟦X⟧) * PowerSeries.X ^ (e - 1)
          * geomFactor ℚ e
        = PowerSeries.C ((e * orbitCount k p f e : ℕ) : ℚ)
            * (PowerSeries.X ^ (e - 1) * geomFactor ℚ e) := by
      rw [map_natCast]
      push_cast
      ring
    rw [hrw, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    by_cases hle : e - 1 ≤ j
    · rw [if_pos hle, coeff_geomFactor]
      have hdvdiff : e ∣ j - (e - 1) ↔ e ∣ j + 1 := by
        have hsub : j - (e - 1) + e = j + 1 := by omega
        constructor
        · intro hd
          have := Nat.dvd_add hd (dvd_refl e)
          rwa [hsub] at this
        · intro hd
          have := Nat.dvd_sub hd (dvd_refl e)
          rwa [show j + 1 - e = j - (e - 1) from by omega] at this
      by_cases hd : e ∣ j + 1
      · rw [if_pos (hdvdiff.mpr hd), if_pos (Nat.mem_divisors.mpr ⟨hd, Nat.succ_ne_zero j⟩),
          mul_one]
      · rw [if_neg (fun hc => hd (hdvdiff.mp hc)), mul_zero,
          if_neg (fun hc => hd (Nat.mem_divisors.mp hc).1)]
    · rw [if_neg hle, mul_zero, if_neg]
      intro hc
      exact hle (by
        have := Nat.le_of_dvd (Nat.succ_pos j) (Nat.mem_divisors.mp hc).1
        omega)
  rw [eulerLogDeriv, map_sum, Finset.sum_congr rfl hterm,
    Finset.sum_ite_mem]
  have hsubset : (j + 1).divisors ∩ Finset.Icc 1 M = (j + 1).divisors := by
    refine Finset.inter_eq_left.mpr fun e he => ?_
    obtain ⟨hd, _⟩ := Nat.mem_divisors.mp he
    have hle := Nat.le_of_dvd (Nat.succ_pos j) hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hd (Nat.succ_pos j), by omega⟩
  rw [Finset.inter_comm, hsubset, pointCount_eq_sum_orbitCount]
  push_cast
  rfl
theorem coeff_eulerPartialQ_eq (M : ℕ) :
    ∀ m ≤ M, PowerSeries.coeff m (eulerPartialQ k p f M)
      = PowerSeries.coeff m (affineHypersurfaceZetaSeries k p f) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      intro hm
      cases m with
      | zero =>
          rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
            PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_eulerPartialQ,
            affineHypersurfaceZetaSeries, constantCoeff_zetaSeriesOf]
      | succ m =>
          have hW := congrArg (PowerSeries.coeff m) (derivative_eulerPartialQ k p f M)
          rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at hW
          have hZ := coeff_succ_of_isZetaSeries
            (affineHypersurfaceZetaSeries_isZetaSeries k p f) m
          have hsum : ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m,
              PowerSeries.coeff ij.1 (eulerLogDeriv k p f M)
                * PowerSeries.coeff ij.2 (eulerPartialQ k p f M)
              = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m,
                  (affineHypersurfacePointCount k p f ij.1 : ℚ)
                    * PowerSeries.coeff ij.2 (affineHypersurfaceZetaSeries k p f) := by
            refine Finset.sum_congr rfl fun ij hij => ?_
            have hij' : ij.1 + ij.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
            rw [coeff_eulerLogDeriv k p f M ij.1 (by omega), ih ij.2 (by omega) (by omega)]
          rw [hsum] at hW
          have hne : ((m : ℚ) + 1) ≠ 0 := by positivity
          apply mul_right_cancel₀ hne
          rw [hW, hZ]
theorem map_eulerPartialZ (M : ℕ) :
    PowerSeries.map (Int.castRingHom ℚ) (eulerPartialZ k p f M) = eulerPartialQ k p f M := by
  rw [eulerPartialZ, eulerPartialQ, map_prod]
  exact Finset.prod_congr rfl fun e _ => by rw [map_pow, map_geomFactor]
theorem affineHypersurfaceZetaSeries_coeff_integral (m : ℕ) :
    ∃ z : ℤ, PowerSeries.coeff m (affineHypersurfaceZetaSeries k p f) = (z : ℚ) := by
  refine ⟨PowerSeries.coeff m (eulerPartialZ k p f m), ?_⟩
  rw [← coeff_eulerPartialQ_eq k p f m m le_rfl, ← map_eulerPartialZ, PowerSeries.coeff_map]
  rfl
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
theorem norm_natCast_p_lt_one : ‖(p : DworkCyclotomicField k p)‖ < 1 := by
  rw [show (p : DworkCyclotomicField k p)
      = algebraMap (CoefficientField k p) (DworkCyclotomicField k p) (p : CoefficientField k p) by
        simp,
    dworkCyclotomicField_norm_algebraMap]
  exact coefficientField_norm_p_lt_one k p
end FiniteFields.Dwork
end
end
section
noncomputable section
open Filter Topology PowerSeries
namespace FiniteFields.Dwork
section PadicGrowth
variable {K : Type*} [NontriviallyNormedField K]
theorem isPadicEntire_iff_exists_bound (F : K⟦X⟧) :
    IsPadicEntire F ↔
      ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, ∀ n : ℕ, ‖PowerSeries.coeff n F‖ * R ^ n ≤ C := by
  constructor
  · intro hF R hR
    obtain ⟨C, hC⟩ := (hF R hR).bddAbove_range
    exact ⟨C, fun n ↦ hC (Set.mem_range_self n)⟩
  · intro hF R hR
    obtain ⟨C, hC⟩ := hF (2 * R + 1) (by linarith)
    have hR' : (0 : ℝ) < 2 * R + 1 := by linarith
    set ρ : ℝ := R / (2 * R + 1) with hρdef
    have hρ0 : 0 ≤ ρ := div_nonneg hR hR'.le
    have hρ1 : ρ < 1 := by
      rw [hρdef, div_lt_one hR']
      linarith
    have hfactor : (2 * R + 1) * ρ = R := by
      rw [hρdef]
      field_simp
    refine squeeze_zero (g := fun n ↦ C * ρ ^ n) (fun n ↦ by positivity) (fun n ↦ ?_) ?_
    · have hsplit : R ^ n = (2 * R + 1) ^ n * ρ ^ n := by
        rw [← mul_pow, hfactor]
      calc ‖PowerSeries.coeff n F‖ * R ^ n
          = (‖PowerSeries.coeff n F‖ * (2 * R + 1) ^ n) * ρ ^ n := by
            rw [hsplit]; ring
        _ ≤ C * ρ ^ n := mul_le_mul_of_nonneg_right (hC n) (by positivity)
    · simpa using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul C
theorem IsPadicEntire.exists_nonneg_bound {F : K⟦X⟧} (hF : IsPadicEntire F)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖PowerSeries.coeff n F‖ * R ^ n ≤ C := by
  obtain ⟨C, hC⟩ := (isPadicEntire_iff_exists_bound F).1 hF R hR
  refine ⟨C, ?_, hC⟩
  have h0 := hC 0
  simpa using le_trans (norm_nonneg (PowerSeries.coeff 0 F)) (by simpa using h0)
theorem isPadicEntire_of_eventually_zero {F : K⟦X⟧} {N : ℕ}
    (h : ∀ n, N ≤ n → PowerSeries.coeff n F = 0) : IsPadicEntire F := by
  intro R _
  refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ)) (f := atTop))
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [h n hn, norm_zero, zero_mul]
theorem isPadicEntire_one : IsPadicEntire (1 : K⟦X⟧) :=
  isPadicEntire_of_eventually_zero (N := 1) fun n hn ↦ by
    rw [PowerSeries.coeff_one, if_neg (by omega)]
end PadicGrowth
section PadicGrowthUltra
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
theorem norm_sum_mul_le_of_forall {ι : Type*} (s : Finset ι) (f : ι → K) {r C : ℝ}
    (hr : 0 ≤ r) (hC : 0 ≤ C) (h : ∀ i ∈ s, ‖f i‖ * r ≤ C) :
    ‖∑ i ∈ s, f i‖ * r ≤ C := by
  rcases eq_or_lt_of_le hr with hr0 | hr0
  · rw [← hr0, mul_zero]
    exact hC
  · rw [← le_div_iff₀ hr0]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (M := K) (by positivity) ?_
    intro i hi
    rw [le_div_iff₀ hr0]
    exact h i hi
theorem IsPadicEntire.mul {F G : K⟦X⟧} (hF : IsPadicEntire F) (hG : IsPadicEntire G) :
    IsPadicEntire (F * G) := by
  rw [isPadicEntire_iff_exists_bound]
  intro R hR
  obtain ⟨CF, hCF0, hCF⟩ := hF.exists_nonneg_bound R hR
  obtain ⟨CG, hCG0, hCG⟩ := hG.exists_nonneg_bound R hR
  refine ⟨CF * CG, fun n ↦ ?_⟩
  rw [PowerSeries.coeff_mul]
  refine norm_sum_mul_le_of_forall _ _ (by positivity) (by positivity) ?_
  intro ij hij
  have hsum : ij.1 + ij.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [norm_mul]
  calc ‖PowerSeries.coeff ij.1 F‖ * ‖PowerSeries.coeff ij.2 G‖ * R ^ n
      = (‖PowerSeries.coeff ij.1 F‖ * R ^ ij.1) *
          (‖PowerSeries.coeff ij.2 G‖ * R ^ ij.2) := by
        rw [← hsum, pow_add]; ring
    _ ≤ CF * CG :=
        mul_le_mul (hCF ij.1) (hCG ij.2) (by positivity) hCF0
end PadicGrowthUltra
section PadicGrowthComplete
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
end PadicGrowthComplete
end FiniteFields.Dwork
end
end
section
noncomputable section
open Filter Topology PowerSeries
namespace FiniteFields.Dwork
section ZetaSeries
private theorem constantCoeff_countingZetaLog (N : ℕ → ℕ) :
    PowerSeries.constantCoeff (countingZetaLog N) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, countingZetaLog, PowerSeries.coeff_mk]
  simp
private theorem derivative_countingZetaLog (N : ℕ → ℕ) :
    PowerSeries.derivative ℚ (countingZetaLog N) = countingSeries N := by
  ext n
  rw [PowerSeries.coeff_derivative, countingZetaLog, PowerSeries.coeff_mk, coeff_countingSeries]
  have hne : (n : ℚ) + 1 ≠ 0 := by positivity
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
  field_simp
  push_cast
  ring
private theorem constantCoeff_countingZetaSeries (N : ℕ → ℕ) :
    PowerSeries.constantCoeff (countingZetaSeries N) = 1 := by
  rw [countingZetaSeries, ← PowerSeries.coeff_zero_eq_constantCoeff,
    PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero'
      (constantCoeff_countingZetaLog N)), finsum_eq_single _ 0]
  · simp
  · intro e he
    simp [he, constantCoeff_countingZetaLog]
private theorem derivative_countingZetaSeries (N : ℕ → ℕ) :
    PowerSeries.derivative ℚ (countingZetaSeries N) = countingSeries N * countingZetaSeries N := by
  rw [countingZetaSeries, PowerSeries.derivative_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_countingZetaLog N)),
    PowerSeries.derivative_exp, derivative_countingZetaLog, mul_comm]
private theorem countingZetaSeries_isZetaSeries (N : ℕ → ℕ) :
    IsZetaSeries N (countingZetaSeries N) :=
  ⟨constantCoeff_countingZetaSeries N, derivative_countingZetaSeries N⟩
variable (k₀ : Type) (p : ℕ) [Fact p.Prime] [Field k₀] [CharP k₀ p] [Finite k₀]
variable {d : ℕ}
theorem toricHypersurfaceZetaSeries_isZetaSeries (f : MonomialIndex d →₀ k₀) :
    IsZetaSeries (toricHypersurfacePointCount k₀ p f) (toricHypersurfaceZetaSeries k₀ p f) :=
  countingZetaSeries_isZetaSeries _
theorem toricHypersurfaceZetaSeries_unique (f : MonomialIndex d →₀ k₀) {Z : ℚ⟦X⟧}
    (hZ : IsZetaSeries (toricHypersurfacePointCount k₀ p f) Z) :
    Z = toricHypersurfaceZetaSeries k₀ p f :=
  hZ.unique (toricHypersurfaceZetaSeries_isZetaSeries k₀ p f)
end ZetaSeries
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries
namespace FiniteFields.Dwork
section ZetaCalculus
theorem countingSeries_add (N₁ N₂ : ℕ → ℕ) :
    countingSeries (fun n ↦ N₁ n + N₂ n) = countingSeries N₁ + countingSeries N₂ := by
  ext n
  rw [map_add, coeff_countingSeries, coeff_countingSeries, coeff_countingSeries, Nat.cast_add]
theorem zetaSeriesOf_add (N₁ N₂ : ℕ → ℕ) :
    zetaSeriesOf (fun n ↦ N₁ n + N₂ n) = zetaSeriesOf N₁ * zetaSeriesOf N₂ := by
  refine (zetaSeriesOf_isZetaSeries _).unique ⟨?_, ?_⟩
  · rw [map_mul, constantCoeff_zetaSeriesOf, constantCoeff_zetaSeriesOf, one_mul]
  · rw [(PowerSeries.derivative ℚ).leibniz, smul_eq_mul, smul_eq_mul,
      derivative_zetaSeriesOf, derivative_zetaSeriesOf, countingSeries_add]
    ring
end ZetaCalculus
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries
namespace FiniteFields.Dwork
section MeromorphicCalculus
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
omit [IsUltrametricDist K] in
theorem isPadicMeromorphic_one : IsPadicMeromorphic (1 : K⟦X⟧) :=
  ⟨1, 1, isPadicEntire_one, isPadicEntire_one, by simp, by rw [mul_one]⟩
theorem IsPadicMeromorphic.mul {F G : K⟦X⟧} (hF : IsPadicMeromorphic F)
    (hG : IsPadicMeromorphic G) : IsPadicMeromorphic (F * G) := by
  obtain ⟨GF, HF, hGF, hHF, hHF1, hFid⟩ := hF
  obtain ⟨GG, HG, hGG, hHG, hHG1, hGid⟩ := hG
  refine ⟨GF * GG, HF * HG, hGF.mul hGG, hHF.mul hHG, ?_, ?_⟩
  · rw [map_mul, hHF1, hHG1, one_mul]
  · calc HF * HG * (F * G) = (HF * F) * (HG * G) := by ring
      _ = GF * GG := by rw [hFid, hGid]
theorem isPadicMeromorphic_prod {ι : Type*} (s : Finset ι) (F : ι → K⟦X⟧)
    (hF : ∀ i ∈ s, IsPadicMeromorphic (F i)) : IsPadicMeromorphic (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPadicMeromorphic_one
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (hF i (Finset.mem_insert_self i s)).mul
        (ih fun j hj ↦ hF j (Finset.mem_insert_of_mem hj))
end MeromorphicCalculus
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries
namespace FiniteFields.Dwork
section Strata
variable {d : ℕ}
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
theorem affineHypersurfacePointCount_eq_sum_strata (f : MvPolynomial (Fin d) k) (n : ℕ) :
    affineHypersurfacePointCount k p f n
      = ∑ S : Finset (Fin d), toricHypersurfacePointCount k p (stratumPoly k f S) n := by
  classical
  rw [affineHypersurfacePointCount_eq_tupleCount,
    ← Nat.card_congr (Equiv.sigmaFiberEquiv fun x : AffineHypersurfaceTuples k p f n ↦
      coordinateSupport k p x.1),
    Nat.card_sigma]
  exact Finset.sum_congr rfl fun S _ ↦ Nat.card_congr (stratumEquiv k p f n S)
end Strata
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries
namespace FiniteFields.Dwork
section Presentation
theorem exists_normalized_rationalPresentation {F : ℚ⟦X⟧} (hF : IsRationalPowerSeries F) :
    ∃ P Q : Polynomial ℚ, Q.eval 0 = 1 ∧ IsCoprime P Q ∧ (Q : ℚ⟦X⟧) * F = (P : ℚ⟦X⟧) := by
  classical
  obtain ⟨P₀, Q₀, hQ₀ne, hQ₀0, hid⟩ := hF
  set g : Polynomial ℚ := GCDMonoid.gcd P₀ Q₀ with hg
  have hgne : g ≠ 0 := by
    rw [hg]
    intro hzero
    exact hQ₀ne ((gcd_eq_zero_iff P₀ Q₀).mp hzero).2
  set P₁ : Polynomial ℚ := P₀ / g with hP₁
  set Q₁ : Polynomial ℚ := Q₀ / g with hQ₁
  have hPg : g * P₁ = P₀ :=
    EuclideanDomain.mul_div_cancel' hgne (gcd_dvd_left P₀ Q₀)
  have hQg : g * Q₁ = Q₀ :=
    EuclideanDomain.mul_div_cancel' hgne (gcd_dvd_right P₀ Q₀)
  have hcop : IsCoprime P₁ Q₁ := isCoprime_div_gcd_div_gcd hQ₀ne
  have hQ₁0 : Q₁.eval 0 ≠ 0 := by
    intro hzero
    apply hQ₀0
    rw [← hQg, Polynomial.eval_mul, hzero, mul_zero]
  have hcancel : (Q₁ : ℚ⟦X⟧) * F = (P₁ : ℚ⟦X⟧) := by
    have hgcoe : ((g : Polynomial ℚ) : ℚ⟦X⟧) ≠ 0 := by
      simpa using hgne
    refine mul_left_cancel₀ hgcoe ?_
    calc ((g : Polynomial ℚ) : ℚ⟦X⟧) * ((Q₁ : ℚ⟦X⟧) * F)
        = ((g * Q₁ : Polynomial ℚ) : ℚ⟦X⟧) * F := by push_cast; ring
      _ = ((Q₀ : Polynomial ℚ) : ℚ⟦X⟧) * F := by rw [hQg]
      _ = ((P₀ : Polynomial ℚ) : ℚ⟦X⟧) := hid
      _ = ((g * P₁ : Polynomial ℚ) : ℚ⟦X⟧) := by rw [hPg]
      _ = ((g : Polynomial ℚ) : ℚ⟦X⟧) * (P₁ : ℚ⟦X⟧) := by push_cast; ring
  set c : ℚ := (Q₁.eval 0)⁻¹ with hc
  have hcne : c ≠ 0 := inv_ne_zero hQ₁0
  refine ⟨Polynomial.C c * P₁, Polynomial.C c * Q₁, ?_, ?_, ?_⟩
  · rw [Polynomial.eval_mul, Polynomial.eval_C, hc, inv_mul_cancel₀ hQ₁0]
  · obtain ⟨a, b, hab⟩ := hcop
    refine ⟨Polynomial.C c⁻¹ * a, Polynomial.C c⁻¹ * b, ?_⟩
    calc Polynomial.C c⁻¹ * a * (Polynomial.C c * P₁)
          + Polynomial.C c⁻¹ * b * (Polynomial.C c * Q₁)
        = (Polynomial.C c⁻¹ * Polynomial.C c) * (a * P₁ + b * Q₁) := by ring
      _ = Polynomial.C (c⁻¹ * c) * 1 := by rw [← Polynomial.C_mul, hab]
      _ = 1 := by rw [inv_mul_cancel₀ hcne, map_one, mul_one]
  · rw [Polynomial.coe_mul, Polynomial.coe_mul, Polynomial.coe_C, mul_assoc, hcancel]
end Presentation
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries
namespace FiniteFields.Dwork
section Meromorphy
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {d : ℕ}
theorem affineHypersurfaceZetaSeries_eq_prod_strata (f : MvPolynomial (Fin d) k) :
    affineHypersurfaceZetaSeries k p f
      = ∏ S : Finset (Fin d), toricHypersurfaceZetaSeries k p (stratumPoly k f S) := by
  classical
  have hcarrier : affineHypersurfaceZetaSeries k p f
      = zetaSeriesOf (affineHypersurfacePointCount k p f) := rfl
  have hfun : affineHypersurfacePointCount k p f
      = fun n ↦ ∑ S : Finset (Fin d), toricHypersurfacePointCount k p (stratumPoly k f S) n :=
    funext fun n ↦ affineHypersurfacePointCount_eq_sum_strata k p f n
  rw [hcarrier, hfun, zetaSeriesOf_sum]
  exact Finset.prod_congr rfl fun S _ ↦
    toricHypersurfaceZetaSeries_unique k p _ (zetaSeriesOf_isZetaSeries _)
theorem affineHypersurfaceZeta_isPadicMeromorphic (f : MvPolynomial (Fin d) k) :
    IsPadicMeromorphic
      (PowerSeries.map (algebraMap ℚ (DworkCyclotomicField k p))
        (affineHypersurfaceZetaSeries k p f)) := by
  classical
  rw [affineHypersurfaceZetaSeries_eq_prod_strata, map_prod]
  exact isPadicMeromorphic_prod _ _ fun S _ ↦
    dworkToricZeta_isPadicMeromorphic k p (stratumPoly k f S) (totalDegreeWeight (S.card + 1))
end Meromorphy
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries
namespace FiniteFields.Dwork
section ResidueNorm
open scoped NNReal Valued
private theorem dworkCyclotomicField_norm_natCast_p_eq (k : Type) (p : ℕ) [Fact p.Prime] [Field k]
    [CharP k p] [Finite k] : ‖(p : DworkCyclotomicField k p)‖ = ((p : ℝ))⁻¹ := by
  rw [show (p : DworkCyclotomicField k p) =
      algebraMap (CoefficientField k p) (DworkCyclotomicField k p)
        (p : CoefficientField k p) by simp,
    dworkCyclotomicField_norm_algebraMap,
    coefficientField_norm_eq,
    coefficientField_valuation_p,
    WithZeroMulInt.toNNReal_neg_apply]
  · have hunzero :
        WithZero.unzero (show WithZero.exp (-1 : ℤ) ≠ 0 by simp)
          = Multiplicative.ofAdd (-1 : ℤ) := by
      rw [← WithZero.coe_inj]
      simp [WithZero.exp]
    rw [hunzero]
    simp
  · simp
end ResidueNorm
section Rationality
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {d : ℕ}
theorem affineHypersurfaceZeta_isRational (f : MvPolynomial (Fin d) k) :
    IsRationalPowerSeries (affineHypersurfaceZetaSeries k p f) := by
  classical
  choose z hz using affineHypersurfaceZetaSeries_coeff_integral k p f
  have hB : (1 : ℚ) ≤ ((Nat.card k ^ d : ℕ) : ℚ) := by
    have hone : 1 ≤ Nat.card k ^ d := Nat.one_le_pow _ _ Nat.card_pos
    exact_mod_cast hone
  refine borelDwork_rationalityCriterion (K := DworkCyclotomicField k p) (Fact.out : p.Prime)
    (dworkCyclotomicField_norm_natCast_p_eq k p).ge (norm_natCast_p_lt_one k p) _ z hz
    (C := 1) hB (fun m ↦ ?_) (affineHypersurfaceZeta_isPadicMeromorphic k p f)
  obtain ⟨h0, hle⟩ := affineHypersurfaceZeta_archimedeanGrowth k p f m
  rw [abs_of_nonneg h0, one_mul]
  exact hle
end Rationality
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries
namespace FiniteFields.Dwork
section DworkAffineRationality
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {d : ℕ}
theorem affineHypersurfaceZeta_isZetaSeries_pointCount (f : MvPolynomial (Fin d) k) :
    IsZetaSeries
      (fun n ↦ pointCount (k := k) (p := p) (affineHypersurfaceScheme k f)
        (affineHypersurfaceHom k f) n)
      (affineHypersurfaceZetaSeries k p f) :=
  affineHypersurfaceZetaSeries_isZetaSeries k p f
theorem dworkAffineHypersurfaceZeta_isRational (f : MvPolynomial (Fin d) k) :
    IsZetaSeries
        (fun n ↦ pointCount (k := k) (p := p) (affineHypersurfaceScheme k f)
          (affineHypersurfaceHom k f) n)
        (affineHypersurfaceZetaSeries k p f)
      ∧ IsRationalPowerSeries (affineHypersurfaceZetaSeries k p f) :=
  ⟨affineHypersurfaceZeta_isZetaSeries_pointCount k p f,
    affineHypersurfaceZeta_isRational k p f⟩
end DworkAffineRationality
end FiniteFields.Dwork
end
end
section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {d : ℕ}
theorem affineZeroLocusPointCount_eq_tupleCount (F : Finset (MvPolynomial (Fin d) k)) (n : ℕ) :
    affineZeroLocusPointCount k p F n = Nat.card (AffineZeroLocusTuples k p F n) :=
  Nat.card_congr (affineZeroLocusExtensionPointEquiv k p F n)
end FiniteFields.Dwork
end
end
section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {d : ℕ}
section InclusionExclusion
private theorem alternating_indicator_sum {α : Type*} [DecidableEq α] (F : Finset α)
    (P : α → Prop) [DecidablePred P] :
    (∑ S ∈ F.powerset, (-1 : ℤ) ^ S.card * (if ∀ g ∈ S, P g then 1 else 0))
      = if ∀ g ∈ F, ¬ P g then 1 else 0 := by
  have hfil : F.powerset.filter (fun S ↦ ∀ g ∈ S, P g) = (F.filter P).powerset := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hSF, hSP⟩ g hg
      exact Finset.mem_filter.mpr ⟨hSF hg, hSP g hg⟩
    · intro h
      refine ⟨?_, ?_⟩
      · intro g hg
        exact (Finset.mem_filter.mp (h hg)).1
      · intro g hg
        exact (Finset.mem_filter.mp (h hg)).2
  have hterm : ∀ S : Finset α, (-1 : ℤ) ^ S.card * (if ∀ g ∈ S, P g then 1 else 0)
      = if ∀ g ∈ S, P g then (-1 : ℤ) ^ S.card else 0 := by
    intro S
    rw [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl fun S _ ↦ hterm S, ← Finset.sum_filter, hfil,
    Finset.sum_powerset_neg_one_pow_card]
  simp only [Finset.filter_eq_empty_iff]
omit [Finite k] in
theorem aeval_prod_ne_zero_iff {K : Type} [CommRing K] [IsDomain K] [Algebra k K]
    (S : Finset (MvPolynomial (Fin d) k)) (x : Fin d → K) :
    MvPolynomial.aeval x (∏ g ∈ S, g) ≠ 0 ↔ ∀ g ∈ S, MvPolynomial.aeval x g ≠ 0 := by
  rw [map_prod, Finset.prod_ne_zero_iff]
theorem affineZeroLocusPointCount_inclusionExclusion (F : Finset (MvPolynomial (Fin d) k))
    (n : ℕ) :
    (affineZeroLocusPointCount k p F n : ℤ)
      = (∑ S ∈ F.powerset, (-1 : ℤ) ^ S.card) * ((Nat.card k ^ (n + 1)) ^ d : ℤ)
        + ∑ S ∈ F.powerset, (-1 : ℤ) ^ (S.card + 1)
            * (affineHypersurfacePointCount k p (∏ g ∈ S, g) n : ℤ) := by
  classical
  letI : Fintype (Fin d → Extension k p n) := Fintype.ofFinite _
  have hamb : ((Finset.univ : Finset (Fin d → Extension k p n)).card : ℤ)
      = ((Nat.card k ^ (n + 1)) ^ d : ℤ) := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact_mod_cast congrArg (fun m : ℕ ↦ (m : ℤ)) (natCard_affinePoints k p d n)
  have hM : ∀ S : Finset (MvPolynomial (Fin d) k),
      (affineHypersurfacePointCount k p (∏ g ∈ S, g) n : ℤ)
        = ((Finset.univ.filter
            fun x : Fin d → Extension k p n ↦ MvPolynomial.aeval x (∏ g ∈ S, g) = 0).card : ℤ) := by
    intro S
    rw [affineHypersurfacePointCount_eq_tupleCount, Nat.card_eq_fintype_card]
    norm_cast
    exact Fintype.card_subtype _
  have hN : (affineZeroLocusPointCount k p F n : ℤ)
      = ((Finset.univ.filter
          fun x : Fin d → Extension k p n ↦ ∀ g ∈ F, MvPolynomial.aeval x g = 0).card : ℤ) := by
    rw [affineZeroLocusPointCount_eq_tupleCount, Nat.card_eq_fintype_card]
    norm_cast
    exact Fintype.card_subtype _
  have hU : ∀ S : Finset (MvPolynomial (Fin d) k),
      ((Nat.card k ^ (n + 1)) ^ d : ℤ)
          - (affineHypersurfacePointCount k p (∏ g ∈ S, g) n : ℤ)
        = ∑ x : Fin d → Extension k p n,
            (if ∀ g ∈ S, MvPolynomial.aeval x g ≠ 0 then (1 : ℤ) else 0) := by
    intro S
    have hcompl := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin d → Extension k p n)))
      (fun x ↦ MvPolynomial.aeval x (∏ g ∈ S, g) = 0)
    have hfil : (Finset.univ.filter
        fun x : Fin d → Extension k p n ↦ ¬ MvPolynomial.aeval x (∏ g ∈ S, g) = 0)
        = Finset.univ.filter
            fun x : Fin d → Extension k p n ↦ ∀ g ∈ S, MvPolynomial.aeval x g ≠ 0 :=
      Finset.filter_congr fun x _ ↦ aeval_prod_ne_zero_iff (k := k) S x
    have hQ : ((Finset.univ.filter fun x : Fin d → Extension k p n ↦
          ∀ g ∈ S, MvPolynomial.aeval x g ≠ 0).card : ℤ)
        = ∑ x : Fin d → Extension k p n,
            (if ∀ g ∈ S, MvPolynomial.aeval x g ≠ 0 then (1 : ℤ) else 0) := by
      rw [Finset.card_filter]
      push_cast
      rfl
    rw [← hQ, hM S, ← hamb, ← hcompl, hfil]
    push_cast
    ring
  rw [hN]
  have hkey : ((Finset.univ.filter
        fun x : Fin d → Extension k p n ↦ ∀ g ∈ F, MvPolynomial.aeval x g = 0).card : ℤ)
      = ∑ S ∈ F.powerset, (-1 : ℤ) ^ S.card
          * (((Nat.card k ^ (n + 1)) ^ d : ℤ)
              - (affineHypersurfacePointCount k p (∏ g ∈ S, g) n : ℤ)) := by
    have hstep : ∀ S ∈ F.powerset, (-1 : ℤ) ^ S.card
        * (((Nat.card k ^ (n + 1)) ^ d : ℤ)
            - (affineHypersurfacePointCount k p (∏ g ∈ S, g) n : ℤ))
        = ∑ x : Fin d → Extension k p n, (-1 : ℤ) ^ S.card
            * (if ∀ g ∈ S, MvPolynomial.aeval x g ≠ 0 then (1 : ℤ) else 0) := by
      intro S _
      rw [hU S, Finset.mul_sum]
    rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [alternating_indicator_sum F (fun g ↦ MvPolynomial.aeval x g ≠ 0)]
    simp
  rw [hkey]
  have hexp : ∀ S ∈ F.powerset, (-1 : ℤ) ^ S.card
      * (((Nat.card k ^ (n + 1)) ^ d : ℤ)
          - (affineHypersurfacePointCount k p (∏ g ∈ S, g) n : ℤ))
      = (-1 : ℤ) ^ S.card * ((Nat.card k ^ (n + 1)) ^ d : ℤ)
        + (-1 : ℤ) ^ (S.card + 1) * (affineHypersurfacePointCount k p (∏ g ∈ S, g) n : ℤ) := by
    intro S _
    rw [pow_succ]
    ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, ← Finset.sum_mul]
theorem affineZeroLocusPointCount_inclusionExclusion_of_nonempty
    {F : Finset (MvPolynomial (Fin d) k)} (hF : F.Nonempty) (n : ℕ) :
    (affineZeroLocusPointCount k p F n : ℤ)
      = ∑ S ∈ F.powerset, (-1 : ℤ) ^ (S.card + 1)
          * (affineHypersurfacePointCount k p (∏ g ∈ S, g) n : ℤ) := by
  rw [affineZeroLocusPointCount_inclusionExclusion,
    Finset.sum_powerset_neg_one_pow_card_of_nonempty hF, zero_mul, zero_add]
theorem affineZeroLocusPointCount_empty (n : ℕ) :
    affineZeroLocusPointCount k p (∅ : Finset (MvPolynomial (Fin d) k)) n
      = (Nat.card k ^ (n + 1)) ^ d := by
  have hequiv : AffineZeroLocusTuples k p (∅ : Finset (MvPolynomial (Fin d) k)) n
      ≃ AffinePoints k p d n :=
    Equiv.subtypeUnivEquiv fun _ g hg ↦ absurd hg (Finset.notMem_empty g)
  rw [affineZeroLocusPointCount_eq_tupleCount, Nat.card_congr hequiv]
  exact natCard_affinePoints k p d n
end InclusionExclusion
end FiniteFields.Dwork
end
end
section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {d : ℕ}
section ZetaProduct
theorem affineZeroLocusZetaSeries_isZetaSeries (F : Finset (MvPolynomial (Fin d) k)) :
    IsZetaSeries
      (fun n ↦ pointCount (k := k) (p := p) (affineZeroLocusScheme k F)
        (affineZeroLocusHom k F) n)
      (affineZeroLocusZetaSeries k p F) :=
  zetaSeriesOf_isZetaSeries _
theorem affineZeroLocusPointCount_parity_split {F : Finset (MvPolynomial (Fin d) k)}
    (hF : F.Nonempty) (n : ℕ) :
    affineZeroLocusPointCount k p F n
        + ∑ S ∈ F.powerset.filter (fun S ↦ Even S.card),
            affineHypersurfacePointCount k p (∏ g ∈ S, g) n
      = ∑ S ∈ F.powerset.filter (fun S ↦ ¬ Even S.card),
          affineHypersurfacePointCount k p (∏ g ∈ S, g) n := by
  classical
  have hZ := affineZeroLocusPointCount_inclusionExclusion_of_nonempty k p hF n
  rw [← Finset.sum_filter_add_sum_filter_not F.powerset (fun S ↦ Even S.card)] at hZ
  have heven : ∀ S ∈ F.powerset.filter (fun S ↦ Even S.card),
      (-1 : ℤ) ^ (S.card + 1) * (affineHypersurfacePointCount k p (∏ g ∈ S, g) n : ℤ)
        = -(affineHypersurfacePointCount k p (∏ g ∈ S, g) n : ℤ) := by
    intro S hS
    obtain ⟨_, hpar⟩ := Finset.mem_filter.mp hS
    rw [pow_succ, hpar.neg_one_pow]
    ring
  have hodd : ∀ S ∈ F.powerset.filter (fun S ↦ ¬ Even S.card),
      (-1 : ℤ) ^ (S.card + 1) * (affineHypersurfacePointCount k p (∏ g ∈ S, g) n : ℤ)
        = (affineHypersurfacePointCount k p (∏ g ∈ S, g) n : ℤ) := by
    intro S hS
    obtain ⟨_, hpar⟩ := Finset.mem_filter.mp hS
    rw [pow_succ, (Nat.not_even_iff_odd.mp hpar).neg_one_pow]
    ring
  rw [Finset.sum_congr rfl heven, Finset.sum_congr rfl hodd, Finset.sum_neg_distrib] at hZ
  have hcast : ((affineZeroLocusPointCount k p F n
        + ∑ S ∈ F.powerset.filter (fun S ↦ Even S.card),
            affineHypersurfacePointCount k p (∏ g ∈ S, g) n : ℕ) : ℤ)
      = ((∑ S ∈ F.powerset.filter (fun S ↦ ¬ Even S.card),
            affineHypersurfacePointCount k p (∏ g ∈ S, g) n : ℕ) : ℤ) := by
    push_cast
    linarith [hZ]
  exact_mod_cast hcast
theorem affineZeroLocusZeta_product_hypersurfaces {F : Finset (MvPolynomial (Fin d) k)}
    (hF : F.Nonempty) :
    affineZeroLocusZetaSeries k p F
        * ∏ S ∈ F.powerset.filter (fun S ↦ Even S.card),
            affineHypersurfaceZetaSeries k p (∏ g ∈ S, g)
      = ∏ S ∈ F.powerset.filter (fun S ↦ ¬ Even S.card),
          affineHypersurfaceZetaSeries k p (∏ g ∈ S, g) := by
  classical
  have hcounts : (fun n ↦ affineZeroLocusPointCount k p F n
        + ∑ S ∈ F.powerset.filter (fun S ↦ Even S.card),
            affineHypersurfacePointCount k p (∏ g ∈ S, g) n)
      = fun n ↦ ∑ S ∈ F.powerset.filter (fun S ↦ ¬ Even S.card),
          affineHypersurfacePointCount k p (∏ g ∈ S, g) n :=
    funext fun n ↦ affineZeroLocusPointCount_parity_split k p hF n
  have h := congrArg zetaSeriesOf hcounts
  rwa [zetaSeriesOf_add, zetaSeriesOf_sum, zetaSeriesOf_sum] at h
theorem affineHypersurfacePointCount_zero (n : ℕ) :
    affineHypersurfacePointCount k p (0 : MvPolynomial (Fin d) k) n
      = (Nat.card k ^ (n + 1)) ^ d := by
  have hequiv : AffineHypersurfaceTuples k p (0 : MvPolynomial (Fin d) k) n
      ≃ AffinePoints k p d n :=
    Equiv.subtypeUnivEquiv fun _ ↦ map_zero _
  rw [affineHypersurfacePointCount_eq_tupleCount, Nat.card_congr hequiv]
  exact natCard_affinePoints k p d n
theorem affineZeroLocusZetaSeries_empty :
    affineZeroLocusZetaSeries k p (∅ : Finset (MvPolynomial (Fin d) k))
      = affineHypersurfaceZetaSeries k p (0 : MvPolynomial (Fin d) k) := by
  refine congrArg zetaSeriesOf (funext fun n ↦ ?_)
  rw [affineZeroLocusPointCount_empty, affineHypersurfacePointCount_zero]
end ZetaProduct
end FiniteFields.Dwork
end
end
section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {d : ℕ}
section Rationality
omit [Field k] [Finite k] [Fact p.Prime] [CharP k p] in
private theorem constantCoeff_coe_eval_zero (Q : Polynomial ℚ) :
    PowerSeries.constantCoeff (Q : ℚ⟦X⟧) = Q.eval 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
    Polynomial.coeff_zero_eq_eval_zero]
private theorem exists_prod_presentation {ι : Type*} (s : Finset ι) (W : ι → ℚ⟦X⟧)
    (hW : ∀ i ∈ s, IsRationalPowerSeries (W i))
    (hW1 : ∀ i ∈ s, PowerSeries.constantCoeff (W i) = 1) :
    ∃ P Q : Polynomial ℚ, Q.eval 0 = 1 ∧ P.eval 0 = 1 ∧
      (Q : ℚ⟦X⟧) * ∏ i ∈ s, W i = (P : ℚ⟦X⟧) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨1, 1, by simp, by simp, by simp⟩
  | @insert i s hi ih =>
      obtain ⟨P₁, Q₁, hQ₁, _, hid₁⟩ :=
        exists_normalized_rationalPresentation (hW i (Finset.mem_insert_self i s))
      obtain ⟨P₂, Q₂, hQ₂, hP₂, hid₂⟩ :=
        ih (fun j hj ↦ hW j (Finset.mem_insert_of_mem hj))
          (fun j hj ↦ hW1 j (Finset.mem_insert_of_mem hj))
      have hP₁ : P₁.eval 0 = 1 := by
        have hc := congrArg PowerSeries.constantCoeff hid₁
        rw [map_mul, hW1 i (Finset.mem_insert_self i s), mul_one,
          constantCoeff_coe_eval_zero, constantCoeff_coe_eval_zero, hQ₁] at hc
        exact hc.symm
      refine ⟨P₁ * P₂, Q₁ * Q₂, by rw [Polynomial.eval_mul, hQ₁, hQ₂, one_mul],
        by rw [Polynomial.eval_mul, hP₁, hP₂, one_mul], ?_⟩
      rw [Finset.prod_insert hi, Polynomial.coe_mul, Polynomial.coe_mul]
      calc (Q₁ : ℚ⟦X⟧) * (Q₂ : ℚ⟦X⟧) * (W i * ∏ j ∈ s, W j)
          = ((Q₁ : ℚ⟦X⟧) * W i) * ((Q₂ : ℚ⟦X⟧) * ∏ j ∈ s, W j) := by ring
        _ = (P₁ : ℚ⟦X⟧) * (P₂ : ℚ⟦X⟧) := by rw [hid₁, hid₂]
theorem affineZeroLocusZeta_isRational (F : Finset (MvPolynomial (Fin d) k)) :
    IsRationalPowerSeries (affineZeroLocusZetaSeries k p F) := by
  classical
  rcases Finset.eq_empty_or_nonempty F with rfl | hF
  · rw [affineZeroLocusZetaSeries_empty]
    exact (dworkAffineHypersurfaceZeta_isRational k p _).2
  · have hrat : ∀ S : Finset (MvPolynomial (Fin d) k),
        IsRationalPowerSeries (affineHypersurfaceZetaSeries k p (∏ g ∈ S, g)) :=
      fun S ↦ (dworkAffineHypersurfaceZeta_isRational k p _).2
    have hone : ∀ S : Finset (MvPolynomial (Fin d) k),
        PowerSeries.constantCoeff (affineHypersurfaceZetaSeries k p (∏ g ∈ S, g)) = 1 :=
      fun S ↦ constantCoeff_zetaSeriesOf _
    obtain ⟨Pe, Qe, hQe, hPe, hide⟩ :=
      exists_prod_presentation (F.powerset.filter fun S ↦ Even S.card)
        (fun S ↦ affineHypersurfaceZetaSeries k p (∏ g ∈ S, g))
        (fun S _ ↦ hrat S) (fun S _ ↦ hone S)
    obtain ⟨Po, Qo, hQo, _, hido⟩ :=
      exists_prod_presentation (F.powerset.filter fun S ↦ ¬ Even S.card)
        (fun S ↦ affineHypersurfaceZetaSeries k p (∏ g ∈ S, g))
        (fun S _ ↦ hrat S) (fun S _ ↦ hone S)
    have hprod := affineZeroLocusZeta_product_hypersurfaces k p hF
    refine ⟨Qe * Po, Qo * Pe, ?_, ?_, ?_⟩
    · intro hzero
      have := congrArg (Polynomial.eval 0) hzero
      rw [Polynomial.eval_mul, hQo, hPe, one_mul, Polynomial.eval_zero] at this
      exact one_ne_zero this
    · rw [Polynomial.eval_mul, hQo, hPe, one_mul]
      exact one_ne_zero
    · rw [Polynomial.coe_mul, Polynomial.coe_mul]
      calc (Qo : ℚ⟦X⟧) * (Pe : ℚ⟦X⟧) * affineZeroLocusZetaSeries k p F
          = (Qo : ℚ⟦X⟧) * (((Qe : ℚ⟦X⟧)
              * ∏ S ∈ F.powerset.filter (fun S ↦ Even S.card),
                  affineHypersurfaceZetaSeries k p (∏ g ∈ S, g))
              * affineZeroLocusZetaSeries k p F) := by rw [hide]; ring
        _ = (Qe : ℚ⟦X⟧) * ((Qo : ℚ⟦X⟧)
              * ∏ S ∈ F.powerset.filter (fun S ↦ ¬ Even S.card),
                  affineHypersurfaceZetaSeries k p (∏ g ∈ S, g)) := by
              rw [← hprod]; ring
        _ = (Qe : ℚ⟦X⟧) * (Po : ℚ⟦X⟧) := by rw [hido]
end Rationality
end FiniteFields.Dwork
end
end
section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {d : ℕ}
section Presentation
variable {A B : Type} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
omit [Finite k] [Fact p.Prime] [CharP k p] in
theorem specAlgEquiv_hom_over (e : A ≃ₐ[k] B) :
    (specAlgEquiv k e).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k A))
      = Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
  rw [specAlgEquiv, ← Spec.map_comp]
  congr 1
  ext a
  show e (algebraMap k A a) = algebraMap k B a
  exact e.commutes a
omit [Finite k] [Fact p.Prime] [CharP k p] in
theorem affineFiniteType_reducedPresentation (A : Type) [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] :
    ∃ (m : ℕ) (F : Finset (MvPolynomial (Fin m) k)) (_ : A ≃ₐ[k] AffineZeroLocusRing k F)
      (ι : affineZeroLocusScheme k F ≅ Spec (.of A)),
      ι.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) = affineZeroLocusHom k F := by
  obtain ⟨m, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (inferInstance : Algebra.FiniteType k A)
  obtain ⟨F, hF⟩ := Ideal.fg_of_isNoetherianRing (RingHom.ker (f : MvPolynomial (Fin m) k →+* A))
  have hker : Ideal.span (F : Set (MvPolynomial (Fin m) k))
      = RingHom.ker (f : MvPolynomial (Fin m) k →+* A) := hF
  let e : A ≃ₐ[k] AffineZeroLocusRing k F :=
    (Ideal.quotientKerAlgEquivOfSurjective hf).symm.trans
      (Ideal.quotientEquivAlgOfEq k hker.symm)
  refine ⟨m, F, e, specAlgEquiv k e, ?_⟩
  exact specAlgEquiv_hom_over k e
theorem pointCount_eq_of_presentation (A : Type) [CommRing A] [Algebra k A]
    {m : ℕ} {F : Finset (MvPolynomial (Fin m) k)}
    (ι : affineZeroLocusScheme k F ≅ Spec (.of A))
    (hι : ι.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) = affineZeroLocusHom k F)
    [∀ n, Finite (ExtensionPoint (k := k) (p := p) (Spec (.of A))
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) n)] (n : ℕ) :
    pointCount (k := k) (p := p) (Spec (.of A))
        (Spec.map (CommRingCat.ofHom (algebraMap k A))) n
      = affineZeroLocusPointCount k p F n := by
  have hinv : ι.symm.hom ≫ affineZeroLocusHom k F
      = Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
    rw [Iso.symm_hom, ← hι]
    exact Iso.inv_hom_id_assoc ι _
  show Nat.card (ExtensionPoint (k := k) (p := p) (Spec (.of A))
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) n)
    = Nat.card (ExtensionPoint (k := k) (p := p) (affineZeroLocusScheme k F)
      (affineZeroLocusHom k F) n)
  exact Nat.card_congr (extensionPointCongr k p ι.symm hinv n)
theorem affineFiniteTypeZeta_isRational (A : Type) [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] {Z : ℚ⟦X⟧}
    (hZ : IsZetaSeries
      (fun n ↦ pointCount (k := k) (p := p) (Spec (.of A))
        (Spec.map (CommRingCat.ofHom (algebraMap k A))) n) Z) :
    IsRationalPowerSeries Z := by
  obtain ⟨m, F, _, ι, hι⟩ := affineFiniteType_reducedPresentation k A
  have hcounts : (fun n ↦ pointCount (k := k) (p := p) (Spec (.of A))
        (Spec.map (CommRingCat.ofHom (algebraMap k A))) n)
      = affineZeroLocusPointCount k p F :=
    funext fun n ↦ pointCount_eq_of_presentation k p A ι hι n
  rw [hcounts] at hZ
  rw [hZ.unique (affineZeroLocusZetaSeries_isZetaSeries k p F)]
  exact affineZeroLocusZeta_isRational k p F
end Presentation
end FiniteFields.Dwork
end
end
section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
section RationalClosure
variable {K : Type*} [Field K]
theorem constantCoeff_coe_eq_eval_zero (Q : Polynomial K) :
    PowerSeries.constantCoeff (Q : K⟦X⟧) = Q.eval 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
    Polynomial.coeff_zero_eq_eval_zero]
theorem IsRationalPowerSeries.mul {F G : K⟦X⟧} (hF : IsRationalPowerSeries F)
    (hG : IsRationalPowerSeries G) : IsRationalPowerSeries (F * G) := by
  obtain ⟨P₁, Q₁, hQ₁ne, hQ₁0, hid₁⟩ := hF
  obtain ⟨P₂, Q₂, hQ₂ne, hQ₂0, hid₂⟩ := hG
  refine ⟨P₁ * P₂, Q₁ * Q₂, mul_ne_zero hQ₁ne hQ₂ne, ?_, ?_⟩
  · rw [Polynomial.eval_mul]
    exact mul_ne_zero hQ₁0 hQ₂0
  · rw [Polynomial.coe_mul, Polynomial.coe_mul]
    calc (Q₁ : K⟦X⟧) * (Q₂ : K⟦X⟧) * (F * G)
        = ((Q₁ : K⟦X⟧) * F) * ((Q₂ : K⟦X⟧) * G) := by ring
      _ = (P₁ : K⟦X⟧) * (P₂ : K⟦X⟧) := by rw [hid₁, hid₂]
theorem IsRationalPowerSeries.inv_of_constantCoeff {F : K⟦X⟧} (hF : IsRationalPowerSeries F)
    (h0 : PowerSeries.constantCoeff F ≠ 0) : IsRationalPowerSeries F⁻¹ := by
  obtain ⟨P, Q, hQne, hQ0, hid⟩ := hF
  have hP0 : P.eval 0 ≠ 0 := by
    have hc := congrArg PowerSeries.constantCoeff hid
    rw [map_mul, constantCoeff_coe_eq_eval_zero, constantCoeff_coe_eq_eval_zero] at hc
    rw [← hc]
    exact mul_ne_zero hQ0 h0
  refine ⟨Q, P, ?_, hP0, ?_⟩
  · intro hzero
    exact hP0 (by rw [hzero, Polynomial.eval_zero])
  · calc (P : K⟦X⟧) * F⁻¹ = ((Q : K⟦X⟧) * F) * F⁻¹ := by rw [hid]
      _ = (Q : K⟦X⟧) * (F * F⁻¹) := by ring
      _ = (Q : K⟦X⟧) := by rw [PowerSeries.mul_inv_cancel F h0, mul_one]
theorem IsRationalPowerSeries.div_of_constantCoeff {F G : K⟦X⟧} (hF : IsRationalPowerSeries F)
    (hG : IsRationalPowerSeries G) (h0 : PowerSeries.constantCoeff G ≠ 0) :
    IsRationalPowerSeries (F * G⁻¹) :=
  hF.mul (hG.inv_of_constantCoeff h0)
theorem isRationalPowerSeries_one : IsRationalPowerSeries (1 : K⟦X⟧) :=
  ⟨1, 1, one_ne_zero, by simp, by simp⟩
theorem isRationalPowerSeries_prod {ι : Type*} (s : Finset ι) (W : ι → K⟦X⟧)
    (h : ∀ i ∈ s, IsRationalPowerSeries (W i)) : IsRationalPowerSeries (∏ i ∈ s, W i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isRationalPowerSeries_one
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (h i (Finset.mem_insert_self i s)).mul
        (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))
theorem isRationalPowerSeries_of_mul_eq {Z W Y : K⟦X⟧} (hW : IsRationalPowerSeries W)
    (hY : IsRationalPowerSeries Y) (h0 : PowerSeries.constantCoeff W ≠ 0) (h : Z * W = Y) :
    IsRationalPowerSeries Z := by
  have hZ : Z = Y * W⁻¹ := by
    rw [← h]
    calc Z = Z * (W * W⁻¹) := by rw [PowerSeries.mul_inv_cancel W h0, mul_one]
      _ = Z * W * W⁻¹ := by ring
  rw [hZ]
  exact hY.div_of_constantCoeff hW h0
end RationalClosure
end FiniteFields.Dwork
end
end
section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
namespace FiniteAffineIntersectionCover
variable {X : Scheme} (𝒞 : FiniteAffineIntersectionCover X)
attribute [instance] fintypeI₀ decEqI₀
theorem mem_coverInter {S : Finset 𝒞.I₀} {x : X} :
    x ∈ 𝒞.coverInter S ↔ ∀ i ∈ S, x ∈ 𝒞.chart i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [coverInter]
  | @insert i s hi ih =>
      rw [coverInter, Finset.inf_insert] at *
      simp only [Finset.mem_insert, forall_eq_or_imp]
      constructor
      · intro hx
        obtain ⟨h1, h2⟩ := hx
        exact ⟨h1, ih.mp h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, ih.mpr h2⟩
theorem isAffineOpen_coverInter {S : Finset 𝒞.I₀} (hS : S.Nonempty) :
    IsAffineOpen (𝒞.coverInter S) := 𝒞.isAffineOpen_inf S hS
end FiniteAffineIntersectionCover
end FiniteFields.Dwork
end
end
section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
section Charts
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {X : Scheme} (π : X ⟶ Spec (.of k))
theorem pointCount_opens_eq (U : X.Opens) (n : ℕ)
    [Finite (ExtensionPoint (k := k) (p := p) X π n)] :
    pointCount (k := k) (p := p) U.toScheme (U.ι ≫ π) n
      = Nat.card {P : ExtensionPoint (k := k) (p := p) X π n //
          extensionPointBase k p P ∈ U} :=
  Nat.card_congr (extensionPoint_mem_affineCover k p π U n)
end Charts
end FiniteFields.Dwork
end
end
section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
section InclusionExclusion
private theorem alternating_nonempty_subset_sum {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset α) (hT : T.Nonempty) :
    ∑ S ∈ (Finset.univ : Finset α).powerset.filter (fun S ↦ S.Nonempty),
        (-1 : ℤ) ^ (S.card + 1) * (if S ⊆ T then 1 else 0) = 1 := by
  classical
  have hterm : ∀ S : Finset α, (-1 : ℤ) ^ (S.card + 1) * (if S ⊆ T then 1 else 0)
      = if S ⊆ T then (-1 : ℤ) ^ (S.card + 1) else 0 := by
    intro S
    rw [mul_ite, mul_one, mul_zero]
  have hfil : ((Finset.univ : Finset α).powerset.filter (fun S ↦ S.Nonempty)).filter
      (fun S ↦ S ⊆ T) = T.powerset.filter (fun S ↦ S.Nonempty) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
    tauto
  rw [Finset.sum_congr rfl fun S _ ↦ hterm S, ← Finset.sum_filter, hfil]
  have hsplit := Finset.sum_filter_add_sum_filter_not T.powerset (fun S ↦ S.Nonempty)
    (fun S ↦ (-1 : ℤ) ^ (S.card + 1))
  have hempty : T.powerset.filter (fun S ↦ ¬ S.Nonempty) = {∅} := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton,
      Finset.not_nonempty_iff_eq_empty]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨by rw [h]; exact Finset.empty_subset T, h⟩⟩
  have htotal : ∑ S ∈ T.powerset, (-1 : ℤ) ^ (S.card + 1) = 0 := by
    have hneg : ∀ S : Finset α, (-1 : ℤ) ^ (S.card + 1) = -((-1 : ℤ) ^ S.card) := by
      intro S
      rw [pow_succ]
      ring
    rw [Finset.sum_congr rfl fun S _ ↦ hneg S, Finset.sum_neg_distrib,
      Finset.sum_powerset_neg_one_pow_card_of_nonempty hT, neg_zero]
  rw [hempty, Finset.sum_singleton, Finset.card_empty] at hsplit
  norm_num at hsplit
  omega
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {X : Scheme} (π : X ⟶ Spec (.of k))
theorem pointCount_affineCover_inclusionExclusion (𝒞 : FiniteAffineIntersectionCover X) (n : ℕ)
    [Finite (ExtensionPoint (k := k) (p := p) X π n)] :
    (pointCount (k := k) (p := p) X π n : ℤ)
      = ∑ S ∈ (Finset.univ : Finset 𝒞.I₀).powerset.filter (fun S ↦ S.Nonempty),
          (-1 : ℤ) ^ (S.card + 1)
            * (pointCount (k := k) (p := p) (𝒞.coverInter S).toScheme
                ((𝒞.coverInter S).ι ≫ π) n : ℤ) := by
  classical
  letI : Fintype (ExtensionPoint (k := k) (p := p) X π n) := Fintype.ofFinite _
  have hM : ∀ S : Finset 𝒞.I₀,
      (pointCount (k := k) (p := p) (𝒞.coverInter S).toScheme ((𝒞.coverInter S).ι ≫ π) n : ℤ)
        = ((Finset.univ.filter fun P : ExtensionPoint (k := k) (p := p) X π n ↦
            ∀ i ∈ S, extensionPointBase k p P ∈ 𝒞.chart i).card : ℤ) := by
    intro S
    rw [pointCount_opens_eq k p π]
    have hcongr : Nat.card {P : ExtensionPoint (k := k) (p := p) X π n //
          extensionPointBase k p P ∈ 𝒞.coverInter S}
        = Nat.card {P : ExtensionPoint (k := k) (p := p) X π n //
            ∀ i ∈ S, extensionPointBase k p P ∈ 𝒞.chart i} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun P ↦ 𝒞.mem_coverInter)
    rw [hcongr, Nat.card_eq_fintype_card]
    norm_cast
    exact Fintype.card_subtype _
  have hexp : ∀ S : Finset 𝒞.I₀,
      ((Finset.univ.filter fun P : ExtensionPoint (k := k) (p := p) X π n ↦
          ∀ i ∈ S, extensionPointBase k p P ∈ 𝒞.chart i).card : ℤ)
        = ∑ P : ExtensionPoint (k := k) (p := p) X π n,
            (if S ⊆ Finset.univ.filter fun i ↦ extensionPointBase k p P ∈ 𝒞.chart i
              then (1 : ℤ) else 0) := by
    intro S
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun P _ ↦ ?_
    congr 1
    simp only [Finset.subset_iff, Finset.mem_filter, Finset.mem_univ, true_and]
  have hterm : ∀ S ∈ (Finset.univ : Finset 𝒞.I₀).powerset.filter (fun S ↦ S.Nonempty),
      (-1 : ℤ) ^ (S.card + 1)
          * (pointCount (k := k) (p := p) (𝒞.coverInter S).toScheme
              ((𝒞.coverInter S).ι ≫ π) n : ℤ)
        = ∑ P : ExtensionPoint (k := k) (p := p) X π n, (-1 : ℤ) ^ (S.card + 1)
            * (if S ⊆ Finset.univ.filter fun i ↦ extensionPointBase k p P ∈ 𝒞.chart i
                then (1 : ℤ) else 0) := by
    intro S _
    rw [hM S, hexp S, Finset.mul_sum]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  have hpt : ∀ P : ExtensionPoint (k := k) (p := p) X π n,
      ∑ S ∈ (Finset.univ : Finset 𝒞.I₀).powerset.filter (fun S ↦ S.Nonempty),
          (-1 : ℤ) ^ (S.card + 1)
            * (if S ⊆ Finset.univ.filter fun i ↦ extensionPointBase k p P ∈ 𝒞.chart i
                then (1 : ℤ) else 0) = 1 := by
    intro P
    obtain ⟨i, hi⟩ := 𝒞.covers (extensionPointBase k p P)
    exact alternating_nonempty_subset_sum _
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  rw [Finset.sum_congr rfl fun P _ ↦ hpt P, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_univ, ← Nat.card_eq_fintype_card]
  rfl
theorem pointCount_affineCover_parity_split (𝒞 : FiniteAffineIntersectionCover X) (n : ℕ)
    [Finite (ExtensionPoint (k := k) (p := p) X π n)] :
    pointCount (k := k) (p := p) X π n
        + ∑ S ∈ ((Finset.univ : Finset 𝒞.I₀).powerset.filter (fun S ↦ S.Nonempty)).filter
            (fun S ↦ Even S.card),
            pointCount (k := k) (p := p) (𝒞.coverInter S).toScheme
              ((𝒞.coverInter S).ι ≫ π) n
      = ∑ S ∈ ((Finset.univ : Finset 𝒞.I₀).powerset.filter (fun S ↦ S.Nonempty)).filter
          (fun S ↦ ¬ Even S.card),
          pointCount (k := k) (p := p) (𝒞.coverInter S).toScheme
            ((𝒞.coverInter S).ι ≫ π) n := by
  classical
  have hZ := pointCount_affineCover_inclusionExclusion k p π 𝒞 n
  rw [← Finset.sum_filter_add_sum_filter_not
    ((Finset.univ : Finset 𝒞.I₀).powerset.filter (fun S ↦ S.Nonempty))
    (fun S ↦ Even S.card)] at hZ
  have heven : ∀ S ∈ ((Finset.univ : Finset 𝒞.I₀).powerset.filter (fun S ↦ S.Nonempty)).filter
      (fun S ↦ Even S.card),
      (-1 : ℤ) ^ (S.card + 1) * (pointCount (k := k) (p := p) (𝒞.coverInter S).toScheme
          ((𝒞.coverInter S).ι ≫ π) n : ℤ)
        = -(pointCount (k := k) (p := p) (𝒞.coverInter S).toScheme
            ((𝒞.coverInter S).ι ≫ π) n : ℤ) := by
    intro S hS
    obtain ⟨_, hpar⟩ := Finset.mem_filter.mp hS
    rw [pow_succ, hpar.neg_one_pow]
    ring
  have hodd : ∀ S ∈ ((Finset.univ : Finset 𝒞.I₀).powerset.filter (fun S ↦ S.Nonempty)).filter
      (fun S ↦ ¬ Even S.card),
      (-1 : ℤ) ^ (S.card + 1) * (pointCount (k := k) (p := p) (𝒞.coverInter S).toScheme
          ((𝒞.coverInter S).ι ≫ π) n : ℤ)
        = (pointCount (k := k) (p := p) (𝒞.coverInter S).toScheme
            ((𝒞.coverInter S).ι ≫ π) n : ℤ) := by
    intro S hS
    obtain ⟨_, hpar⟩ := Finset.mem_filter.mp hS
    rw [pow_succ, (Nat.not_even_iff_odd.mp hpar).neg_one_pow]
    ring
  rw [Finset.sum_congr rfl heven, Finset.sum_congr rfl hodd, Finset.sum_neg_distrib] at hZ
  have hcast : ((pointCount (k := k) (p := p) X π n
        + ∑ S ∈ ((Finset.univ : Finset 𝒞.I₀).powerset.filter (fun S ↦ S.Nonempty)).filter
            (fun S ↦ Even S.card),
            pointCount (k := k) (p := p) (𝒞.coverInter S).toScheme
              ((𝒞.coverInter S).ι ≫ π) n : ℕ) : ℤ)
      = ((∑ S ∈ ((Finset.univ : Finset 𝒞.I₀).powerset.filter (fun S ↦ S.Nonempty)).filter
            (fun S ↦ ¬ Even S.card),
            pointCount (k := k) (p := p) (𝒞.coverInter S).toScheme
              ((𝒞.coverInter S).ι ≫ π) n : ℕ) : ℤ) := by
    push_cast
    linarith [hZ]
  exact_mod_cast hcast
theorem zetaSeries_affineCover_product (𝒞 : FiniteAffineIntersectionCover X)
    [∀ n, Finite (ExtensionPoint (k := k) (p := p) X π n)] :
    zetaSeriesOf (fun n ↦ pointCount (k := k) (p := p) X π n)
        * ∏ S ∈ ((Finset.univ : Finset 𝒞.I₀).powerset.filter (fun S ↦ S.Nonempty)).filter
            (fun S ↦ Even S.card),
            zetaSeriesOf (fun n ↦ pointCount (k := k) (p := p) (𝒞.coverInter S).toScheme
              ((𝒞.coverInter S).ι ≫ π) n)
      = ∏ S ∈ ((Finset.univ : Finset 𝒞.I₀).powerset.filter (fun S ↦ S.Nonempty)).filter
          (fun S ↦ ¬ Even S.card),
          zetaSeriesOf (fun n ↦ pointCount (k := k) (p := p) (𝒞.coverInter S).toScheme
            ((𝒞.coverInter S).ι ≫ π) n) := by
  classical
  have hcounts : (fun n ↦ pointCount (k := k) (p := p) X π n
        + ∑ S ∈ ((Finset.univ : Finset 𝒞.I₀).powerset.filter (fun S ↦ S.Nonempty)).filter
            (fun S ↦ Even S.card),
            pointCount (k := k) (p := p) (𝒞.coverInter S).toScheme
              ((𝒞.coverInter S).ι ≫ π) n)
      = fun n ↦ ∑ S ∈ ((Finset.univ : Finset 𝒞.I₀).powerset.filter (fun S ↦ S.Nonempty)).filter
          (fun S ↦ ¬ Even S.card),
          pointCount (k := k) (p := p) (𝒞.coverInter S).toScheme
            ((𝒞.coverInter S).ι ≫ π) n :=
    funext fun n ↦ pointCount_affineCover_parity_split k p π 𝒞 n
  have h := congrArg zetaSeriesOf hcounts
  rwa [zetaSeriesOf_add, zetaSeriesOf_sum, zetaSeriesOf_sum] at h
end InclusionExclusion
end FiniteFields.Dwork
end
end
section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
section Construction
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
theorem affineOpenZeta_isRational {X : Scheme} (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π]
    (V : X.Opens) (hV : IsAffineOpen V)
    [∀ n, Finite (ExtensionPoint (k := k) (p := p) X π n)] :
    IsRationalPowerSeries
      (zetaSeriesOf (fun n ↦ pointCount (k := k) (p := p) V.toScheme (V.ι ≫ π) n)) := by
  classical
  haveI : IsAffine V.toScheme := hV
  set φ : CommRingCat.of k ⟶ Γ(X, V) :=
    (Scheme.ΓSpecIso (.of k)).inv ≫ π.appLE ⊤ V le_top with hφdef
  letI : Algebra k (Γ(X, V) : Type) := φ.hom.toAlgebra
  haveI : Algebra.FiniteType k (Γ(X, V) : Type) := by
    have h1 : (π.appLE ⊤ V le_top).hom.FiniteType :=
      π.finiteType_appLE (isAffineOpen_top _) hV le_top
    have h2 : φ.hom.FiniteType := by
      rw [hφdef]
      exact (RingHom.finiteType_respectsIso.cancel_left_isIso
        (Scheme.ΓSpecIso (.of k)).inv (π.appLE ⊤ V le_top)).mpr h1
    exact RingHom.finiteType_algebraMap.mp h2
  have hred : Spec.map φ = hV.fromSpec ≫ π := by
    rw [hφdef, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
    exact IsAffineOpen.SpecMap_appLE_fromSpec π _ hV le_top
  have hcompat : hV.isoSpec.hom
      ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Γ(X, V) : Type))) = V.ι ≫ π := by
    have hid : CommRingCat.ofHom (algebraMap k (Γ(X, V) : Type)) = φ := rfl
    rw [hid, hred, ← IsAffineOpen.isoSpec_inv_ι hV, Category.assoc, Iso.hom_inv_id_assoc]
  have hcount : ∀ n, pointCount (k := k) (p := p) V.toScheme (V.ι ≫ π) n
      = pointCount (k := k) (p := p) (Spec (.of (Γ(X, V) : Type)))
          (Spec.map (CommRingCat.ofHom (algebraMap k (Γ(X, V) : Type)))) n := fun n ↦
    Nat.card_congr (extensionPointCongr k p hV.isoSpec hcompat n)
  refine affineFiniteTypeZeta_isRational k p (Γ(X, V) : Type) ?_
  have hfun : (fun n ↦ pointCount (k := k) (p := p) (Spec (.of (Γ(X, V) : Type)))
        (Spec.map (CommRingCat.ofHom (algebraMap k (Γ(X, V) : Type)))) n)
      = fun n ↦ pointCount (k := k) (p := p) V.toScheme (V.ι ≫ π) n :=
    funext fun n ↦ (hcount n).symm
  rw [hfun]
  exact zetaSeriesOf_isZetaSeries _
theorem separatedFiniteTypeZeta_isRational_of_reduced {X : Scheme} (π : X ⟶ Spec (.of k))
    [QuasiCompact π] [IsSeparated π] [LocallyOfFiniteType π]
    [∀ n, Finite (ExtensionPoint (k := k) (p := p) X π n)] :
    IsRationalPowerSeries
      (zetaSeriesOf (fun n ↦ pointCount (k := k) (p := p) X π n)) := by
  classical
  set 𝒞 := finiteAffineIntersectionCoverOfSeparatedFiniteType π with h𝒞
  have hrat : ∀ S ∈ (Finset.univ : Finset 𝒞.I₀).powerset.filter (fun S ↦ S.Nonempty),
      IsRationalPowerSeries
        (zetaSeriesOf (fun n ↦ pointCount (k := k) (p := p) (𝒞.coverInter S).toScheme
          ((𝒞.coverInter S).ι ≫ π) n)) := by
    intro S hS
    obtain ⟨_, hne⟩ := Finset.mem_filter.mp hS
    exact affineOpenZeta_isRational k p π (𝒞.coverInter S) (𝒞.isAffineOpen_coverInter hne)
  refine isRationalPowerSeries_of_mul_eq ?_ ?_ ?_
    (zetaSeries_affineCover_product k p π 𝒞)
  · refine isRationalPowerSeries_prod _ _ fun S hS ↦ hrat S ?_
    exact (Finset.mem_filter.mp hS).1
  · refine isRationalPowerSeries_prod _ _ fun S hS ↦ hrat S ?_
    exact (Finset.mem_filter.mp hS).1
  · rw [map_prod]
    refine fun hzero ↦ one_ne_zero (α := ℚ) ?_
    rw [← Finset.prod_eq_one fun S (_ : S ∈ ((Finset.univ : Finset 𝒞.I₀).powerset.filter
      (fun S ↦ S.Nonempty)).filter (fun S ↦ Even S.card)) ↦
        constantCoeff_zetaSeriesOf (fun n ↦ pointCount (k := k) (p := p)
          (𝒞.coverInter S).toScheme ((𝒞.coverInter S).ι ≫ π) n)]
    exact hzero
end Construction
end FiniteFields.Dwork
end
end
section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
section Reduction
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {X : Scheme} (π : X ⟶ Spec (.of k))
theorem pointCount_reduction [LocallyOfFiniteType π] [QuasiCompact π] (n : ℕ) :
    pointCount (k := k) (p := p) (reduction X) (reductionι X ≫ π) n
      = pointCount (k := k) (p := p) X π n :=
  Nat.card_congr (extensionPointReductionEquiv k p π n)
theorem zetaSeries_reduction [LocallyOfFiniteType π] [QuasiCompact π]
    {Z W : PowerSeries ℚ}
    (hZ : IsZetaSeries
      (fun n ↦ pointCount (k := k) (p := p) (reduction X) (reductionι X ≫ π) n) Z)
    (hW : IsZetaSeries (fun n ↦ pointCount (k := k) (p := p) X π n) W) :
    Z = W := by
  refine hZ.unique ?_
  have hN : (fun n ↦ pointCount (k := k) (p := p) X π n)
      = fun n ↦ pointCount (k := k) (p := p) (reduction X) (reductionι X ≫ π) n :=
    funext fun n ↦ (pointCount_reduction k p π n).symm
  rw [← hN]
  exact hW
theorem zetaSeriesOf_reduction [LocallyOfFiniteType π] [QuasiCompact π] :
    zetaSeriesOf (fun n ↦ pointCount (k := k) (p := p) (reduction X) (reductionι X ≫ π) n)
      = zetaSeriesOf (fun n ↦ pointCount (k := k) (p := p) X π n) :=
  zetaSeries_reduction k p π (zetaSeriesOf_isZetaSeries _) (zetaSeriesOf_isZetaSeries _)
end Reduction
section General
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {X : Scheme} (π : X ⟶ Spec (.of k))
theorem separatedFiniteTypeZetaSeries_isZetaSeries (hπ : Schemes.FiniteType π) :
    IsZetaSeries (fun n ↦ pointCount_of_finiteType k p X π hπ n)
      (separatedFiniteTypeZetaSeries k p π hπ) :=
  zetaSeriesOf_isZetaSeries _
theorem separatedFiniteTypeZetaSeries_eq (hπ : Schemes.FiniteType π)
    [LocallyOfFiniteType π] [QuasiCompact π] :
    separatedFiniteTypeZetaSeries k p π hπ
      = zetaSeriesOf (fun n ↦ pointCount (k := k) (p := p) X π n) :=
  rfl
theorem separatedFiniteTypeZeta_isRational (hπ : Schemes.FiniteType π) (hsep : IsSeparated π) :
    IsZetaSeries (fun n ↦ pointCount_of_finiteType k p X π hπ n)
        (separatedFiniteTypeZetaSeries k p π hπ)
      ∧ IsRationalPowerSeries (separatedFiniteTypeZetaSeries k p π hπ) := by
  letI : LocallyOfFiniteType π := hπ.1
  letI : QuasiCompact π := hπ.2
  letI : IsSeparated π := hsep
  refine ⟨separatedFiniteTypeZetaSeries_isZetaSeries k p π hπ, ?_⟩
  rw [separatedFiniteTypeZetaSeries_eq k p π hπ, ← zetaSeriesOf_reduction k p π]
  exact separatedFiniteTypeZeta_isRational_of_reduced k p (reductionι X ≫ π)
theorem separatedFiniteTypeZeta_rationalPresentation (hπ : Schemes.FiniteType π)
    (hsep : IsSeparated π) :
    ∃ P Q : Polynomial ℚ,
      Q.eval 0 = 1 ∧ IsCoprime P Q ∧
      IsZetaSeries (fun n ↦ pointCount_of_finiteType k p X π hπ n)
        (separatedFiniteTypeZetaSeries k p π hπ) ∧
      (Q : PowerSeries ℚ) * separatedFiniteTypeZetaSeries k p π hπ = (P : PowerSeries ℚ) := by
  obtain ⟨hZS, hrat⟩ := separatedFiniteTypeZeta_isRational k p π hπ hsep
  obtain ⟨P, Q, hQ0, hcop, hid⟩ := exists_normalized_rationalPresentation hrat
  exact ⟨P, Q, hQ0, hcop, hZS, hid⟩
end General
end FiniteFields.Dwork
end
end
section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
section DworkGeneralRationality
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {X : Scheme} (π : X ⟶ Spec (.of k))
theorem dworkGeneralZeta_rationalPresentation (hπ : Schemes.FiniteType π) (hsep : IsSeparated π) :
    ∃ P Q : Polynomial ℚ,
      Q.eval 0 = 1 ∧ IsCoprime P Q ∧
      IsZetaSeries (fun n ↦ pointCount_of_finiteType k p X π hπ n)
        (separatedFiniteTypeZetaSeries k p π hπ) ∧
      (Q : PowerSeries ℚ) * separatedFiniteTypeZetaSeries k p π hπ = (P : PowerSeries ℚ) :=
  separatedFiniteTypeZeta_rationalPresentation k p π hπ hsep
end DworkGeneralRationality
end FiniteFields.Dwork
end
end
open FiniteFields
open CategoryTheory AlgebraicGeometry PowerSeries
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {X : Scheme} (π : X ⟶ Spec (.of k))
theorem solution (hπ : Schemes.FiniteType π) (hsep : IsSeparated π) :
    ∃ P Q : Polynomial ℚ,
      Q.eval 0 = 1 ∧ IsCoprime P Q ∧
      IsZetaSeries (fun n ↦ pointCount_of_finiteType k p X π hπ n)
        (Dwork.separatedFiniteTypeZetaSeries k p π hπ) ∧
      (Q : PowerSeries ℚ) * Dwork.separatedFiniteTypeZetaSeries k p π hπ = (P : PowerSeries ℚ) :=
  Dwork.dworkGeneralZeta_rationalPresentation k p π hπ hsep
