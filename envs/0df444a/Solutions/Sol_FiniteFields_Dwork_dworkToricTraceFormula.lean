-- Prove2me | solution 1 for FiniteFields.Dwork.dworkToricTraceFormula
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T06:59:14.786975+00:00
-- url     : https://prove2.me/submissions/81140caf-09e5-41df-8172-f743e97c0707

import Mathlib
import Definitions.Def_FiniteFields_Dwork_TraceFormula
import Theorems.Thm_FiniteFields_Dwork_coefficientFieldFrobenius_coefficientRing
import Theorems.Thm_FiniteFields_Dwork_dworkPowerSeriesEval_rescale
import Theorems.Thm_FiniteFields_Dwork_ramifiedCoefficientFrobenius_symm_pow_residueDegree
import Theorems.Thm_FiniteFields_Dwork_tracePower_dworkQFrobeniusNuclearOperator_tendsto
import Theorems.Thm_FiniteFields_Dwork_ramifiedTeichmullerLift_norm_of_ne_zero
import Theorems.Thm_FiniteFields_Dwork_hasSum_dworkSplittingValue
import Theorems.Thm_FiniteFields_Dwork_dworkTraceAdditiveCharacter_ne_zero
import Theorems.Thm_FiniteFields_Dwork_dworkSplittingValue_frobeniusProduct
import Theorems.Thm_FiniteFields_Dwork_norm_artinHasseEvalAt_eta_sub_one_le
import Theorems.Thm_FiniteFields_Dwork_frobenius_wittTraceTeichmuller
import Theorems.Thm_FiniteFields_Dwork_exists_natCast_approx
section
noncomputable section
namespace FiniteFields
variable (k : Type*) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
theorem natCard_extension (n : ℕ) :
    Nat.card (Extension k p n) = Nat.card k ^ (n + 1) := by
  exact FiniteField.natCard_extension k p (n + 1)
end FiniteFields
end
end
section
noncomputable section
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k]
@[simp]
theorem residueMap_teichmullerLift (x : k) : residueMap k p (teichmullerLift k p x) = x := by
  simp [residueMap, teichmullerLift]
variable [CharP k p]
@[simp]
theorem frobeniusLift_teichmuller (x : k) :
    frobeniusLift k p (teichmullerLift k p x) = teichmullerLift k p (x ^ p) := by
  change WittVector.frobenius (WittVector.teichmuller p x) = WittVector.teichmuller p (x ^ p)
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller]
  rfl
variable [Finite k]
end FiniteFields.Dwork
end
end
section
noncomputable section
open Filter Set Topology
open scoped ZeroAtInfty
namespace FiniteFields.Dwork
variable {K : Type*} [NormedField K]
variable {d : ℕ} (w : PositiveMonomialWeight d)
@[simp]
theorem monomialWeight_monomialFrobenius (q : ℕ) (u : MonomialIndex d) :
    monomialWeight w (monomialFrobenius q u) = q * monomialWeight w u := by
  simp [monomialFrobenius]
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
end FiniteFields.Dwork
end
end
section
noncomputable section
open Polynomial
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
@[simp]
theorem ramifiedCoefficientFrobenius_dworkPrimitiveRoot :
    ramifiedCoefficientFrobenius k p (dworkPrimitiveRoot k p) =
      dworkPrimitiveRoot k p := by
  exact ramifiedCoefficientFrobeniusHom_dworkPrimitiveRoot k p
theorem ramifiedCoefficientFrobenius_isometry :
    Isometry (ramifiedCoefficientFrobenius k p) :=
  AddMonoidHomClass.isometry_of_norm _ (ramifiedCoefficientFrobenius_norm k p)
theorem ramifiedCoefficientFrobenius_continuous :
    Continuous (ramifiedCoefficientFrobenius k p) :=
  (ramifiedCoefficientFrobenius_isometry k p).continuous
end FiniteFields.Dwork
end
end
section
noncomputable section
open Filter Function IsUltrametricDist Metric PowerSeries Set
open scoped NNReal Topology
namespace FiniteFields.Dwork
variable (k : Type*) [Field k]
variable (p : ℕ) [Fact p.Prime] [CharP k p] [Finite k]
theorem dworkArtinHasseEval_eq_tsum (x : DworkCyclotomicField k p) :
    dworkArtinHasseEval k p x =
      ∑' n : ℕ, PowerSeries.coeff n (dworkArtinHasseExponential k p) * x ^ n :=
  rfl
theorem dworkArtinHasseParameter_spec :
    dworkArtinHasseEval k p (dworkArtinHasseParameter k p) =
      dworkPrimitiveRoot k p :=
  (existsUnique_dworkArtinHasseParameter k p).choose_spec.1.2.2
theorem dworkArtinHasseParameter_unique
    {eta : DworkCyclotomicField k p}
    (hetaNorm : ‖eta‖ ≤ ‖dworkRamificationParameter k p‖)
    (hetaLt : ‖eta‖ < 1)
    (hetaSpec : dworkArtinHasseEval k p eta = dworkPrimitiveRoot k p) :
    eta = dworkArtinHasseParameter k p := by
  exact (existsUnique_dworkArtinHasseParameter k p).unique
    ⟨hetaNorm, hetaLt, hetaSpec⟩
    (existsUnique_dworkArtinHasseParameter k p).choose_spec.1
theorem dworkSplittingFunction_coeff (n : ℕ) :
    PowerSeries.coeff n (dworkSplittingFunction k p) =
      dworkArtinHasseParameter k p ^ n *
        PowerSeries.coeff n (dworkArtinHasseExponential k p) := by
  rw [dworkSplittingFunction, PowerSeries.coeff_rescale]
end FiniteFields.Dwork
end
end
section
noncomputable section
open Filter Topology
namespace FiniteFields.Dwork
variable (k : Type*) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {d : ℕ} (w : PositiveMonomialWeight d)
theorem ramifiedCoefficientwiseFrobeniusInv_smul
    (c : DworkCyclotomicField k p)
    (g : RamifiedOverconvergentTateAlgebra k p w) :
    ramifiedCoefficientwiseFrobeniusInv k p w (c • g) =
      (ramifiedCoefficientFrobenius k p).symm c •
        ramifiedCoefficientwiseFrobeniusInv k p w g := by
  apply OverconvergentTateAlgebra.ext
  ext u
  exact map_mul (ramifiedCoefficientFrobenius k p).symm c (g.toSeries u)
private theorem ramifiedCoefficientwiseFrobeniusInvSeries_norm
    (g : OverconvergentSeries (DworkCyclotomicField k p) d w) :
    ‖ramifiedCoefficientwiseFrobeniusInvSeries k p w g‖ = ‖g‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
    ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  apply le_antisymm
  · refine (BoundedContinuousFunction.norm_le (norm_nonneg g.toBCF)).2 ?_
    intro u
    change ‖(ramifiedCoefficientFrobenius k p).symm (g u)‖ ≤ ‖g.toBCF‖
    rw [ramifiedCoefficientFrobenius_symm_norm]
    exact BoundedContinuousFunction.norm_coe_le_norm g.toBCF u
  · refine (BoundedContinuousFunction.norm_le
      (norm_nonneg (ramifiedCoefficientwiseFrobeniusInvSeries k p w g).toBCF)).2 ?_
    intro u
    calc
      ‖g u‖ = ‖(ramifiedCoefficientFrobenius k p).symm (g u)‖ :=
        (ramifiedCoefficientFrobenius_symm_norm k p (g u)).symm
      _ ≤ ‖(ramifiedCoefficientwiseFrobeniusInvSeries k p w g).toBCF‖ :=
        BoundedContinuousFunction.norm_coe_le_norm
          (ramifiedCoefficientwiseFrobeniusInvSeries k p w g).toBCF u
theorem ramifiedCoefficientwiseFrobeniusInv_norm
    (g : RamifiedOverconvergentTateAlgebra k p w) :
    ‖ramifiedCoefficientwiseFrobeniusInv k p w g‖ = ‖g‖ :=
  ramifiedCoefficientwiseFrobeniusInvSeries_norm k p w g.toSeries
theorem ramifiedCoefficientwiseFrobeniusInv_continuous :
    Continuous (ramifiedCoefficientwiseFrobeniusInv k p w :
      RamifiedOverconvergentTateAlgebra k p w →
        RamifiedOverconvergentTateAlgebra k p w) :=
  (AddMonoidHomClass.isometry_of_norm (ramifiedCoefficientwiseFrobeniusInv k p w)
    (ramifiedCoefficientwiseFrobeniusInv_norm k p w)).continuous
end FiniteFields.Dwork
end
end
section
noncomputable section
open Filter Topology
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
variable {d : ℕ} (w : PositiveMonomialWeight d)
theorem cutoffKernel_conjugateKernel_pow (c : DworkCyclotomicField k p) (hc : c ≠ 0)
    (n : MonomialIndex d → ℕ)
    (kernel : InfiniteWeightedKernel (K := DworkCyclotomicField k p) (d := d))
    (bound power : ℕ) (u v : WeightedCutoff w bound) :
    ((cutoffKernel w (conjugateKernel k p c n kernel) bound) ^ power) u v
      = c ^ n v.1 * (c ^ n u.1)⁻¹ * ((cutoffKernel w kernel bound) ^ power) u v := by
  classical
  induction power generalizing u v with
  | zero =>
      simp only [pow_zero, Matrix.one_apply]
      by_cases huv : u = v
      · subst huv
        rw [if_pos rfl, mul_one, mul_inv_cancel₀ (pow_ne_zero _ hc)]
      · rw [if_neg huv, mul_zero]
  | succ power ih =>
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hx : c ^ n x.1 * (c ^ n x.1)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hc)
      rw [ih u x, cutoffKernel_apply, conjugateKernel, cutoffKernel_apply]
      calc c ^ n x.1 * (c ^ n u.1)⁻¹ * ((cutoffKernel w kernel bound ^ power) u x) *
            (c ^ n v.1 * (c ^ n x.1)⁻¹ * kernel x.1 v.1)
          = (c ^ n x.1 * (c ^ n x.1)⁻¹) *
              (c ^ n v.1 * (c ^ n u.1)⁻¹ *
                ((cutoffKernel w kernel bound ^ power) u x * kernel x.1 v.1)) := by ring
        _ = c ^ n v.1 * (c ^ n u.1)⁻¹ *
              ((cutoffKernel w kernel bound ^ power) u x * kernel x.1 v.1) := by
            rw [hx, one_mul]
theorem cutoffKernel_dworkQFrobeniusNormalizedKernel_pow (f : MonomialIndex d →₀ k)
    (bound power : ℕ) (u v : WeightedCutoff w bound) :
    ((cutoffKernel w (dworkQFrobeniusNormalizedKernel k p w f) bound) ^ power) u v
      = dworkRamificationParameter k p ^ dworkQDiagonalExponent k p w f v.1 *
          (dworkRamificationParameter k p ^ dworkQDiagonalExponent k p w f u.1)⁻¹ *
          ((cutoffKernel w (dworkQFrobeniusKernel k p w f) bound) ^ power) u v :=
  cutoffKernel_conjugateKernel_pow k p w _ (dworkRamificationParameter_ne_zero k p) _ _
    bound power u v
theorem cutoffKernel_dworkQFrobeniusNormalizedKernel_pow_diagonal (f : MonomialIndex d →₀ k)
    (bound power : ℕ) (u : WeightedCutoff w bound) :
    ((cutoffKernel w (dworkQFrobeniusNormalizedKernel k p w f) bound) ^ power) u u
      = ((cutoffKernel w (dworkQFrobeniusKernel k p w f) bound) ^ power) u u := by
  rw [cutoffKernel_dworkQFrobeniusNormalizedKernel_pow,
    mul_inv_cancel₀ (pow_ne_zero _ (dworkRamificationParameter_ne_zero k p)), one_mul]
end FiniteFields.Dwork
end
end
section
noncomputable section
namespace FiniteFields.Dwork
open Finset
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
  [Algebra (ZMod p) k]
section PrimeFieldMap
end PrimeFieldMap
section FixedPoints
end FixedPoints
section OrbitSum
end OrbitSum
section Trace
@[simp]
theorem wittPrimeFieldMap_wittTrace (w : CoefficientRing k p) :
    wittPrimeFieldMap k p (wittTrace k p w) = wittFrobeniusOrbitSum k p w :=
  wittPrimeFieldMap_wittTraceFun k p w
end Trace
section Derived
omit [Finite k] [Algebra (ZMod p) k] in
private theorem iterate_frobeniusLift_teichmuller (i : ℕ) (x : k) :
    (frobeniusLift k p)^[i] (teichmullerLift k p x) = teichmullerLift k p (x ^ p ^ i) := by
  induction i with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, frobeniusLift_teichmuller]
      congr 1
      rw [← pow_mul, pow_succ]
theorem wittTrace_teichmuller_eq_frobenius_sum (x : k) :
    wittPrimeFieldMap k p (wittTrace k p (teichmullerLift k p x)) =
      ∑ i ∈ range (Module.finrank (ZMod p) k), teichmullerLift k p (x ^ p ^ i) := by
  rw [wittPrimeFieldMap_wittTrace, wittFrobeniusOrbitSum]
  exact Finset.sum_congr rfl fun i _ => iterate_frobeniusLift_teichmuller k p i x
theorem residueMap_wittTrace_teichmuller (x : k) :
    residueMap k p (wittPrimeFieldMap k p (wittTrace k p (teichmullerLift k p x))) =
      algebraMap (ZMod p) k (Algebra.trace (ZMod p) k x) := by
  rw [wittTrace_teichmuller_eq_frobenius_sum, map_sum,
    FiniteField.algebraMap_trace_eq_sum_pow (K := ZMod p) (L := k)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [residueMap_teichmullerLift, Nat.card_zmod]
end Derived
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries
open scoped Classical
namespace FiniteFields.Dwork
section Product
variable {R K : Type*} [CommRing R] [CommRing K] [Algebra ℚ K] (ι : R →+* K) (p : ℕ)
  [Fact p.Prime] (hR : ∀ n, coeff n (artinHasseSeries K p) ∈ Set.range ι)
theorem artinHasseFactor_index_zero (a : R) :
    artinHasseFactor ι p hR a 0 = PowerSeries.rescale a (artinHasseOver ι p hR) := by
  ext n
  rw [artinHasseFactor, PowerSeries.coeff_expand, pow_zero]
  simp
theorem artinHasseWittSeries_teichmuller (hι : Function.Injective ι) {N : ℕ} (hN : 0 < N)
    (a : R) :
    artinHasseWittSeries ι p hR N (WittVector.teichmuller p a)
      = PowerSeries.rescale a (artinHasseOver ι p hR) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [artinHasseWittSeries, Finset.prod_range_succ']
  rw [Finset.prod_eq_one, one_mul, WittVector.teichmuller_coeff_zero,
    artinHasseFactor_index_zero]
  intro i _
  rw [WittVector.teichmuller_coeff_pos p a (i + 1) (Nat.succ_pos i),
    artinHasseFactor_of_zero ι p hR hι]
theorem truncatedArtinHasseProduct_teichmuller (hι : Function.Injective ι) (N : ℕ) (a : R) :
    truncatedArtinHasseProduct ι p hR hι N (WittVector.teichmuller p a)
      = TruncatedPrincipalUnit.ofSeries (PowerSeries.rescale a (artinHasseOver ι p hR))
          (constantCoeff_rescale_artinHasseOver ι p hR hι a) := by
  rw [truncatedArtinHasseProduct]
  refine (TruncatedPrincipalUnit.ofSeries_eq_ofSeries_iff _ _).mpr fun m hm => ?_
  rw [artinHasseWittSeries_teichmuller ι p hR hι (show 0 < N by omega) a]
end Product
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries
namespace FiniteFields.Dwork
section Formal
variable {R K : Type*} [CommRing R] [CommRing K] [Algebra ℚ K] (ι : R →+* K) (p : ℕ)
  [Fact p.Prime] (hR : ∀ n, coeff n (artinHasseSeries K p) ∈ Set.range ι)
theorem formalArtinHasseProduct_teichmuller (hι : Function.Injective ι) (a : R) :
    formalArtinHasseProduct ι p hR hι (WittVector.teichmuller p a)
      = ⟨PowerSeries.rescale a (artinHasseOver ι p hR),
          constantCoeff_rescale_artinHasseOver ι p hR hι a⟩ := by
  refine formalPrincipalUnit_ext fun N => ?_
  rw [formalArtinHasseProduct_truncate, truncatedArtinHasseProduct_teichmuller]
  rfl
end Formal
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries
namespace FiniteFields.Dwork
section DworkCarrier
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
theorem dworkFormalArtinHasseProduct_teichmuller (a : CoefficientRing k p) :
    dworkFormalArtinHasseProduct k p (WittVector.teichmuller p a)
      = ⟨PowerSeries.rescale a (dworkArtinHasseOver k p),
          constantCoeff_rescale_artinHasseOver _ _ _
            (coefficientRingAlgebraMap_injective k p) a⟩ :=
  formalArtinHasseProduct_teichmuller _ _ _ (coefficientRingAlgebraMap_injective k p) a
end DworkCarrier
end FiniteFields.Dwork
end
end
section
noncomputable section
open scoped BigOperators WithZero
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [hpChar : CharP k p] [Finite k]
attribute [local instance] FiniteFields.Dwork.dw4eResiduePrimeAlgebra
attribute [local instance] FiniteFields.Dwork.dw4eDecidableEq
@[simp]
theorem ramifiedTeichmullerLift_one :
    ramifiedTeichmullerLift k p 1 = 1 := by
  simp [ramifiedTeichmullerLift]
@[simp]
theorem ramifiedTeichmullerLift_mul (x y : k) :
    ramifiedTeichmullerLift k p (x * y) =
      ramifiedTeichmullerLift k p x * ramifiedTeichmullerLift k p y := by
  simp [ramifiedTeichmullerLift]
@[simp]
theorem ramifiedCoefficientFrobenius_ramifiedTeichmullerLift (x : k) :
    ramifiedCoefficientFrobenius k p (ramifiedTeichmullerLift k p x) =
      ramifiedTeichmullerLift k p (x ^ p) := by
  rw [ramifiedTeichmullerLift, ramifiedCoefficientFrobenius_algebraMap,
    coefficientFieldFrobenius_coefficientRing, frobeniusLiftEquiv_apply,
    frobeniusLift_teichmuller]
  rfl
theorem dworkSplittingValue_eq_tsum (x : k) :
    dworkSplittingValue k p x =
      ∑' n : ℕ, PowerSeries.coeff n (dworkSplittingFunction k p) *
        ramifiedTeichmullerLift k p x ^ n :=
  rfl
theorem dworkSplittingValue_eq_dworkArtinHasseEval (x : k) :
    dworkSplittingValue k p x =
      dworkArtinHasseEval k p
        (dworkArtinHasseParameter k p * ramifiedTeichmullerLift k p x) := by
  rw [dworkSplittingValue_eq_tsum, dworkArtinHasseEval_eq_tsum]
  apply tsum_congr
  intro n
  rw [dworkSplittingFunction_coeff, mul_pow]
  ring
section Extension
variable (k₀ : Type) (p₀ : ℕ) [Fact p₀.Prime]
  [Field k₀] [CharP k₀ p₀] [Finite k₀]
attribute [local instance] FiniteFields.Dwork.dw4eExtensionCharP
end Extension
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
theorem map_dworkArtinHasseOver :
    PowerSeries.map (cyclotomicCoefficientMap k p) (dworkArtinHasseOver k p)
      = dworkArtinHasseExponential k p := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_map, dworkArtinHasseOver, cyclotomicCoefficientMap_apply,
    dworkArtinHasseExponential, PowerSeries.coeff_map]
  rw [map_coeff_artinHasseOver (coefficientRingAlgebraMap k p) p
    (artinHasseSeries_mem_range_coefficientRingAlgebraMap k p) n]
  rw [artinHasseSeries, PowerSeries.coeff_map]
  rw [eq_ratCast (algebraMap ℚ (CoefficientField k p)),
    show (algebraMap (CoefficientField k p) (DworkCyclotomicField k p))
        ((coeff n (artinHasseExponential p) : ℚ) : CoefficientField k p)
      = ((coeff n (artinHasseExponential p) : ℚ) : DworkCyclotomicField k p) by
      rw [map_ratCast]]
  rfl
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
omit [Field k] [CharP k p] [Finite k] in
theorem map_rescale' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (c : R) (f : R⟦X⟧) :
    PowerSeries.map φ (PowerSeries.rescale c f)
      = PowerSeries.rescale (φ c) (PowerSeries.map φ f) := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_map, PowerSeries.coeff_rescale, PowerSeries.coeff_rescale,
    PowerSeries.coeff_map, map_mul, map_pow]
theorem artinHasseWittHom_teichmuller (x : k) :
    (Additive.toMul (artinHasseWittHom k p
        (WittVector.teichmuller p (teichmullerLift k p x)))).val
      = dworkSplittingValue k p x := by
  have hval : (mapFormalPrincipalUnitToCyclotomic k p
      (dworkFormalArtinHasseProduct k p
        (WittVector.teichmuller p (teichmullerLift k p x)))).val
      = PowerSeries.rescale (ramifiedTeichmullerLift k p x) (dworkArtinHasseExponential k p) := by
    rw [dworkFormalArtinHasseProduct_teichmuller, val_mapFormalPrincipalUnitToCyclotomic]
    show PowerSeries.map (cyclotomicCoefficientMap k p)
        (PowerSeries.rescale (teichmullerLift k p x) (dworkArtinHasseOver k p)) = _
    rw [map_rescale', map_dworkArtinHasseOver]
    rfl
  rw [toMul_artinHasseWittHom, val_specializationPrincipalUnit, formalArtinHasseSpecialization,
    hval, dworkPowerSeriesEval_rescale, dworkSplittingValue_eq_dworkArtinHasseEval,
    dworkArtinHasseEval, mul_comm]
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
attribute [local instance] FiniteFields.Dwork.dw4e2ResiduePrimeAlgebra
namespace DworkPrincipalUnit
end DworkPrincipalUnit
theorem artinHasseWittUnit_teichmuller (x : k) :
    (artinHasseWittUnit k p (WittVector.teichmuller p (teichmullerLift k p x))).val
      = dworkSplittingValue k p x :=
  artinHasseWittHom_teichmuller k p x
theorem wittTraceTeichmuller_coeff_zero (w : CoefficientRing k p) :
    (wittTraceTeichmuller k p w).coeff 0 = wittPrimeFieldMap k p (wittTrace k p w) := by
  have h : (wittTraceTeichmuller k p w).coeff 0
      = WittVector.constantCoeff (wittTraceTeichmuller k p w) := rfl
  rw [h, wittTraceTeichmuller, map_sum, wittPrimeFieldMap_wittTrace, wittFrobeniusOrbitSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact WittVector.teichmuller_coeff_zero p _
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
theorem artinHasseEvalAt_eta (u : WittVector p (CoefficientRing k p)) :
    artinHasseEvalAt k p u (dworkArtinHasseParameter k p) = (artinHasseWittUnit k p u).val := rfl
theorem norm_coeff_artinHasse_le_one (u : WittVector p (CoefficientRing k p)) (n : ℕ) :
    ‖coeff n (mapFormalPrincipalUnitToCyclotomic k p
      (dworkFormalArtinHasseProduct k p u)).val‖ ≤ 1 :=
  norm_coeff_mapFormalPrincipalUnitToCyclotomic_le_one k p _ n
theorem artinHasseEvalAt_zero {z : DworkCyclotomicField k p} :
    artinHasseEvalAt k p 0 z = 1 := by
  rw [artinHasseEvalAt, dworkFormalArtinHasseProduct_zero, mapFormalPrincipalUnitToCyclotomic_one]
  exact dworkPowerSeriesEval_one k p z
theorem artinHasseEvalAt_add (u v : WittVector p (CoefficientRing k p))
    {z : DworkCyclotomicField k p} (hz : ‖z‖ < 1) :
    artinHasseEvalAt k p (u + v) z = artinHasseEvalAt k p u z * artinHasseEvalAt k p v z := by
  have h := dworkPowerSeriesEval_mul k p z hz
    ⟨_, norm_coeff_artinHasse_le_one k p u⟩ ⟨_, norm_coeff_artinHasse_le_one k p v⟩
  rw [artinHasseEvalAt, dworkFormalArtinHasseProduct_add,
    mapFormalPrincipalUnitToCyclotomic_mul, FormalPrincipalUnit.val_mul]
  exact h
theorem artinHasseEvalAt_nsmul (n : ℕ) (u : WittVector p (CoefficientRing k p))
    {z : DworkCyclotomicField k p} (hz : ‖z‖ < 1) :
    artinHasseEvalAt k p (n • u) z = artinHasseEvalAt k p u z ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, artinHasseEvalAt_zero]
  | succ m ih => rw [succ_nsmul, artinHasseEvalAt_add k p _ _ hz, ih, pow_succ]
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
theorem natCast_p_ne_zero : (p : DworkCyclotomicField k p) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
attribute [local instance] FiniteFields.Dwork.dw4e2TraceLimitResiduePrimeAlgebra
theorem norm_dworkPrimitiveRoot : ‖dworkPrimitiveRoot k p‖ = 1 := by
  have hz : dworkPrimitiveRoot k p ^ p = 1 := (dworkPrimitiveRoot_isPrimitiveRoot k p).pow_eq_one
  have h : ‖dworkPrimitiveRoot k p‖ ^ p = 1 := by rw [← norm_pow, hz, norm_one]
  rcases lt_trichotomy ‖dworkPrimitiveRoot k p‖ 1 with hlt | heq | hgt
  · exact absurd h (ne_of_lt (pow_lt_one₀ (norm_nonneg _) hlt (Fact.out : Nat.Prime p).ne_zero))
  · exact heq
  · exact absurd h (ne_of_gt (one_lt_pow₀ hgt (Fact.out : Nat.Prime p).ne_zero))
theorem artinHasseEvalAt_one :
    artinHasseEvalAt k p 1 (dworkArtinHasseParameter k p) = dworkPrimitiveRoot k p := by
  have hone : (1 : WittVector p (CoefficientRing k p))
      = WittVector.teichmuller p (teichmullerLift k p (1 : k)) := by
    rw [map_one, map_one]
  rw [hone, artinHasseEvalAt_eta, artinHasseWittUnit_teichmuller,
    dworkSplittingValue_eq_dworkArtinHasseEval, ramifiedTeichmullerLift_one, mul_one,
    dworkArtinHasseParameter_spec]
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
attribute [local instance] FiniteFields.Dwork.dw4e2TraceCharacterResiduePrimeAlgebra
theorem dworkPrimitiveRoot_pow_mod (n : ℕ) :
    dworkPrimitiveRoot k p ^ n = dworkPrimitiveRoot k p ^ (n % p) := by
  conv_lhs => rw [← Nat.div_add_mod n p]
  rw [pow_add, pow_mul, (dworkPrimitiveRoot_isPrimitiveRoot k p).pow_eq_one, one_pow, one_mul]
theorem norm_dworkTraceAdditiveCharacter (x : k) :
    ‖dworkTraceAdditiveCharacter k p x‖ = 1 := by
  rw [dworkTraceAdditiveCharacter_apply, norm_pow, norm_dworkPrimitiveRoot, one_pow]
theorem dworkSplittingValue_frobeniusProduct_eq_traceCharacter (x : k) :
    dworkFrobeniusConjugateProduct k p x = dworkTraceAdditiveCharacter k p x := by
  have he : ‖dworkArtinHasseParameter k p‖ < 1 := dworkArtinHasseParameter_norm_lt_one k p
  have hρ1 : ‖(p : DworkCyclotomicField k p)‖ < 1 := norm_natCast_p_lt_one k p
  have hρ0 : 0 < ‖(p : DworkCyclotomicField k p)‖ := norm_pos_iff.mpr (natCast_p_ne_zero k p)
  have hprod : artinHasseEvalAt k p (wittTraceTeichmuller k p (teichmullerLift k p x))
      (dworkArtinHasseParameter k p) = dworkFrobeniusConjugateProduct k p x := by
    rw [artinHasseEvalAt_eta]
    exact dworkSplittingValue_frobeniusProduct k p x
  have hbound : ∀ m : ℕ,
      ‖dworkFrobeniusConjugateProduct k p x - dworkTraceAdditiveCharacter k p x‖
        ≤ ‖(p : DworkCyclotomicField k p)‖ ^ m := by
    intro m
    obtain ⟨N, c, hNc⟩ :=
      exists_natCast_approx k p (wittTrace k p (teichmullerLift k p x)) (2 * m + 2)
    have hDfrob : WittVector.frobenius
        (wittTraceTeichmuller k p (teichmullerLift k p x)
          - (N : WittVector p (CoefficientRing k p)))
        = wittTraceTeichmuller k p (teichmullerLift k p x)
          - (N : WittVector p (CoefficientRing k p)) := by
      rw [map_sub, map_natCast, frobenius_wittTraceTeichmuller]
    have hD0 : (wittTraceTeichmuller k p (teichmullerLift k p x)
          - (N : WittVector p (CoefficientRing k p))).coeff 0
        = (p : CoefficientRing k p) ^ (2 * m + 2) * c := by
      have hcc : (wittTraceTeichmuller k p (teichmullerLift k p x)
            - (N : WittVector p (CoefficientRing k p))).coeff 0
          = WittVector.constantCoeff (wittTraceTeichmuller k p (teichmullerLift k p x)
              - (N : WittVector p (CoefficientRing k p))) := rfl
      rw [hcc, map_sub, map_natCast]
      show (wittTraceTeichmuller k p (teichmullerLift k p x)).coeff 0
        - (N : CoefficientRing k p) = _
      rw [wittTraceTeichmuller_coeff_zero]
      exact hNc
    have hDnorm : ‖cyclotomicCoefficientMap k p
        ((wittTraceTeichmuller k p (teichmullerLift k p x)
          - (N : WittVector p (CoefficientRing k p))).coeff 0)‖
        ≤ ‖(p : DworkCyclotomicField k p)‖ ^ (2 * m + 2) := by
      rw [hD0, map_mul, map_pow, map_natCast, norm_mul, norm_pow]
      calc ‖(p : DworkCyclotomicField k p)‖ ^ (2 * m + 2) *
            ‖cyclotomicCoefficientMap k p c‖
          ≤ ‖(p : DworkCyclotomicField k p)‖ ^ (2 * m + 2) * 1 :=
            mul_le_mul_of_nonneg_left (norm_cyclotomicCoefficientMap_le_one k p c) (by positivity)
        _ = ‖(p : DworkCyclotomicField k p)‖ ^ (2 * m + 2) := mul_one _
    have hy := norm_artinHasseEvalAt_eta_sub_one_le k p _ hDfrob m hDnorm
    have hsplit : artinHasseEvalAt k p (wittTraceTeichmuller k p (teichmullerLift k p x))
          (dworkArtinHasseParameter k p)
        = artinHasseEvalAt k p (wittTraceTeichmuller k p (teichmullerLift k p x)
            - (N : WittVector p (CoefficientRing k p))) (dworkArtinHasseParameter k p)
          * dworkPrimitiveRoot k p ^ N := by
      have hTD : wittTraceTeichmuller k p (teichmullerLift k p x)
          = (wittTraceTeichmuller k p (teichmullerLift k p x)
              - (N : WittVector p (CoefficientRing k p)))
            + (N : WittVector p (CoefficientRing k p)) := by ring
      have hN : ((N : ℕ) : WittVector p (CoefficientRing k p))
          = N • (1 : WittVector p (CoefficientRing k p)) := by rw [nsmul_eq_mul, mul_one]
      conv_lhs => rw [hTD]
      rw [artinHasseEvalAt_add k p _ _ he, hN, artinHasseEvalAt_nsmul k p N _ he,
        artinHasseEvalAt_one]
    have hres : ((N : ZMod p)) = Algebra.trace (ZMod p) k x := by
      apply (algebraMap (ZMod p) k).injective
      have h := congrArg (residueMap k p) hNc
      rw [map_sub, map_mul, map_pow, map_natCast, map_natCast, CharP.cast_eq_zero k p,
        zero_pow (by omega), zero_mul, sub_eq_zero] at h
      rw [map_natCast, ← residueMap_wittTrace_teichmuller k p x]
      exact h.symm
    have hchar : dworkPrimitiveRoot k p ^ N = dworkTraceAdditiveCharacter k p x := by
      rw [dworkTraceAdditiveCharacter_apply, ← hres, ZMod.val_natCast,
        ← dworkPrimitiveRoot_pow_mod]
    rw [← hprod, hsplit, hchar]
    have hfactor : artinHasseEvalAt k p (wittTraceTeichmuller k p (teichmullerLift k p x)
          - (N : WittVector p (CoefficientRing k p))) (dworkArtinHasseParameter k p)
          * dworkTraceAdditiveCharacter k p x - dworkTraceAdditiveCharacter k p x
        = (artinHasseEvalAt k p (wittTraceTeichmuller k p (teichmullerLift k p x)
            - (N : WittVector p (CoefficientRing k p))) (dworkArtinHasseParameter k p) - 1)
          * dworkTraceAdditiveCharacter k p x := by ring
    rw [hfactor, norm_mul, norm_dworkTraceAdditiveCharacter, mul_one]
    exact hy
  have hlim : Filter.Tendsto (fun m : ℕ => ‖(p : DworkCyclotomicField k p)‖ ^ m)
      Filter.atTop (nhds 0) := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1
  have hle : ‖dworkFrobeniusConjugateProduct k p x - dworkTraceAdditiveCharacter k p x‖ ≤ 0 :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  have hzero := le_antisymm hle (norm_nonneg _)
  rwa [norm_eq_zero, sub_eq_zero] at hzero
end FiniteFields.Dwork
end
end
section
noncomputable section
open scoped BigOperators
namespace FiniteFields.Dwork
attribute [local instance] dw4eResiduePrimeAlgebra dw4eExtensionCharP
variable (k₀ : Type) (p₀ : ℕ) [Fact p₀.Prime] [Field k₀] [CharP k₀ p₀] [Finite k₀]
theorem finrank_zmod_extension_eq (n : ℕ) :
    Module.finrank (ZMod p₀) (FiniteFields.Extension k₀ p₀ n)
      = (n + 1) * Module.finrank (ZMod p₀) k₀ := by
  calc
    Module.finrank (ZMod p₀) (FiniteFields.Extension k₀ p₀ n)
        = Module.finrank (ZMod p₀) k₀ * (n + 1) := by
      convert FiniteField.finrank_zmod_extension k₀ p₀ (n + 1) using 1
    _ = (n + 1) * Module.finrank (ZMod p₀) k₀ := Nat.mul_comm _ _
end FiniteFields.Dwork
end
end
section
noncomputable section
open scoped BigOperators
namespace FiniteFields.Dwork
attribute [local instance] dw4eResiduePrimeAlgebra dw4eExtensionCharP
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
theorem dworkFrobeniusConjugateProduct_eq_character (x : k) :
    dworkFrobeniusConjugateProduct k p x = dworkTraceAdditiveCharacter k p x :=
  dworkSplittingValue_frobeniusProduct_eq_traceCharacter k p x
section Extension
variable (k₀ : Type) (p₀ : ℕ) [Fact p₀.Prime] [Field k₀] [CharP k₀ p₀] [Finite k₀]
end Extension
end FiniteFields.Dwork
end
end
section
noncomputable section
open scoped BigOperators
namespace FiniteFields.Dwork
attribute [local instance] dw4eResiduePrimeAlgebra dw4eExtensionCharP
section Eval
variable (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] {d : ℕ}
end Eval
section Torus
variable (k₀ : Type) (p₀ : ℕ) [Fact p₀.Prime] [Field k₀] [CharP k₀ p₀] [Finite k₀]
theorem natCard_affineTorus (d n : ℕ) :
    Nat.card (affineTorus k₀ p₀ d n) = (Nat.card k₀ ^ (n + 1) - 1) ^ d := by
  classical
  have hunit : Nat.card {b : FiniteFields.Extension k₀ p₀ n // b ≠ 0}
      = Nat.card k₀ ^ (n + 1) - 1 := by
    rw [← Nat.card_congr (unitsEquivNeZero (G₀ := FiniteFields.Extension k₀ p₀ n)),
      Nat.card_units, FiniteFields.natCard_extension]
  calc
    Nat.card (affineTorus k₀ p₀ d n)
        = Nat.card (∀ i : Fin d, {b : FiniteFields.Extension k₀ p₀ n // b ≠ 0}) :=
      Nat.card_congr (Equiv.subtypePiEquivPi
        (p := fun (_ : Fin d) (b : FiniteFields.Extension k₀ p₀ n) => b ≠ 0))
    _ = ∏ _i : Fin d, Nat.card {b : FiniteFields.Extension k₀ p₀ n // b ≠ 0} :=
      Nat.card_pi
    _ = (Nat.card k₀ ^ (n + 1) - 1) ^ d := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hunit]
end Torus
section Orthogonality
variable (k₀ : Type) (p₀ : ℕ) [Fact p₀.Prime] [Field k₀] [CharP k₀ p₀] [Finite k₀]
theorem additiveCharacter_orthogonality (n : ℕ)
    [Fintype (FiniteFields.Extension k₀ p₀ n)]
    [DecidableEq (FiniteFields.Extension k₀ p₀ n)]
    (y : FiniteFields.Extension k₀ p₀ n) :
    ∑ x : FiniteFields.Extension k₀ p₀ n,
        dworkTraceAdditiveCharacter (FiniteFields.Extension k₀ p₀ n) p₀ (x * y)
      = if y = 0 then
          ((Nat.card k₀ ^ (n + 1) : ℕ) :
            DworkCyclotomicField (FiniteFields.Extension k₀ p₀ n) p₀)
        else 0 := by
  have hprim : AddChar.IsPrimitive
      (dworkTraceAdditiveCharacter (FiniteFields.Extension k₀ p₀ n) p₀) :=
    AddChar.IsPrimitive.of_ne_one
      (fun h => dworkTraceAdditiveCharacter_ne_zero (FiniteFields.Extension k₀ p₀ n) p₀ h)
  rw [AddChar.sum_mulShift y hprim, Fintype.card_eq_nat_card,
    FiniteFields.natCard_extension]
  split_ifs <;> simp
theorem additiveCharacter_orthogonality_punctured (n : ℕ)
    [Fintype (FiniteFields.Extension k₀ p₀ n)]
    [DecidableEq (FiniteFields.Extension k₀ p₀ n)]
    (y : FiniteFields.Extension k₀ p₀ n) :
    ∑ x ∈ Finset.univ.erase (0 : FiniteFields.Extension k₀ p₀ n),
        dworkTraceAdditiveCharacter (FiniteFields.Extension k₀ p₀ n) p₀ (x * y)
      = (if y = 0 then
          ((Nat.card k₀ ^ (n + 1) : ℕ) :
            DworkCyclotomicField (FiniteFields.Extension k₀ p₀ n) p₀)
        else 0) - 1 := by
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (FiniteFields.Extension k₀ p₀ n))
    (fun x => dworkTraceAdditiveCharacter (FiniteFields.Extension k₀ p₀ n) p₀ (x * y))
    (Finset.mem_univ (0 : FiniteFields.Extension k₀ p₀ n))
  rw [← additiveCharacter_orthogonality k₀ p₀ n y, ← hsplit, zero_mul,
    AddChar.map_zero_eq_one]
  ring
end Orthogonality
section CharacterSum
variable (k₀ : Type) (p₀ : ℕ) [Fact p₀.Prime] [Field k₀] [CharP k₀ p₀] [Finite k₀]
theorem addChar_map_sum {A M ι : Type*} [AddCommMonoid A] [CommMonoid M]
    (psi : AddChar A M) (s : Finset ι) (g : ι -> A) :
    psi (∑ i ∈ s, g i) = ∏ i ∈ s, psi (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
theorem toricHypersurfacePointCount_eq_characterSum {d : ℕ} (f : MonomialIndex d →₀ k₀) (n : ℕ)
    [Fintype (FiniteFields.Extension k₀ p₀ n)]
    [DecidableEq (FiniteFields.Extension k₀ p₀ n)] :
    ((Nat.card k₀ ^ (n + 1) : ℕ) :
        DworkCyclotomicField (FiniteFields.Extension k₀ p₀ n) p₀)
        * (toricHypersurfacePointCount k₀ p₀ f n : _)
      = ((Nat.card k₀ ^ (n + 1) - 1 : ℕ) : _) ^ d
        + ∑ x : affineTorus k₀ p₀ d n,
            ∑ x₀ ∈ Finset.univ.erase (0 : FiniteFields.Extension k₀ p₀ n),
              dworkTraceAdditiveCharacter (FiniteFields.Extension k₀ p₀ n) p₀
                (x₀ * finitePolynomialEval k₀ (FiniteFields.Extension k₀ p₀ n) f
                  (x : Fin d → FiniteFields.Extension k₀ p₀ n)) := by
  classical
  have hpunc : ∀ x : affineTorus k₀ p₀ d n,
      (∑ x₀ ∈ Finset.univ.erase (0 : FiniteFields.Extension k₀ p₀ n),
          dworkTraceAdditiveCharacter (FiniteFields.Extension k₀ p₀ n) p₀
            (x₀ * finitePolynomialEval k₀ (FiniteFields.Extension k₀ p₀ n) f
              (x : Fin d → FiniteFields.Extension k₀ p₀ n)))
        = (if finitePolynomialEval k₀ (FiniteFields.Extension k₀ p₀ n) f
                (x : Fin d → FiniteFields.Extension k₀ p₀ n) = 0 then
              ((Nat.card k₀ ^ (n + 1) : ℕ) :
                DworkCyclotomicField (FiniteFields.Extension k₀ p₀ n) p₀)
            else 0) - 1 :=
    fun x => additiveCharacter_orthogonality_punctured k₀ p₀ n _
  rw [Finset.sum_congr rfl fun x _ => hpunc x, Finset.sum_sub_distrib, Finset.sum_ite,
    Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
    nsmul_eq_mul, mul_one]
  have htorus : (Finset.univ : Finset (affineTorus k₀ p₀ d n)).card
      = (Nat.card k₀ ^ (n + 1) - 1) ^ d := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, natCard_affineTorus]
  have hfil : (Finset.univ.filter fun x : affineTorus k₀ p₀ d n =>
      finitePolynomialEval k₀ (FiniteFields.Extension k₀ p₀ n) f
        (x : Fin d → FiniteFields.Extension k₀ p₀ n) = 0).card
      = toricHypersurfacePointCount k₀ p₀ f n := by
    rw [toricHypersurfacePointCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [htorus, hfil]
  push_cast
  ring
end CharacterSum
section SplittingProduct
variable (k₀ : Type) (p₀ : ℕ) [Fact p₀.Prime] [Field k₀] [CharP k₀ p₀] [Finite k₀]
end SplittingProduct
end FiniteFields.Dwork
end
end
section
noncomputable section
open Polynomial
open scoped NNReal WithZero
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
section BaseChange
variable (K : Type*) [Field K] [CharP K p] [Finite K] (σ : k →+* K)
@[simp]
theorem coefficientFieldBaseChange_coeRingHom (a : WithVal (coefficientValuation k p)) :
    coefficientFieldBaseChange k p K σ (UniformSpace.Completion.coeRingHom a)
      = UniformSpace.Completion.coeRingHom (coefficientValuedBaseChange k p K σ a) :=
  UniformSpace.Completion.mapRingHom_coe
    (coefficientValuedBaseChange_uniformContinuous k p K σ).continuous a
end BaseChange
end FiniteFields.Dwork
end
end
section
noncomputable section
open Polynomial
open scoped NNReal WithZero
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
section CyclotomicLift
variable (K : Type*) [Field K] [CharP K p] [Finite K] [Algebra k K]
attribute [local instance 100] dworkCyclotomicBaseAlgebra
@[simp]
theorem dworkCyclotomicBaseChange_dworkPrimitiveRoot :
    dworkCyclotomicBaseChange k p K (dworkPrimitiveRoot k p) = dworkPrimitiveRoot K p := by
  haveI := neZero_p p
  haveI := neZero_p_coefficientField k p
  have hlift := PowerBasis.lift_gen
    ((dworkPrimitiveRoot_isPrimitiveRoot k p).powerBasis (CoefficientField k p))
    (dworkPrimitiveRoot K p)
    (by simpa only [IsPrimitiveRoot.powerBasis_gen] using aeval_dworkPrimitiveRoot_base k p K)
  exact hlift
end CyclotomicLift
end FiniteFields.Dwork
end
end
section
noncomputable section
open Polynomial
open scoped NNReal WithZero
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
section Transport
variable (K : Type*) [Field K] [CharP K p] [Finite K] [Algebra k K]
attribute [local instance 100] dworkCyclotomicBaseAlgebra
@[simp]
theorem dworkCyclotomicBaseChange_dworkRamificationParameter :
    dworkCyclotomicBaseChange k p K (dworkRamificationParameter k p)
      = dworkRamificationParameter K p := by
  rw [dworkRamificationParameter, dworkRamificationParameter, map_sub, map_one,
    dworkCyclotomicBaseChange_dworkPrimitiveRoot]
theorem dworkCyclotomicBaseChange_dworkArtinHasseExponential_coeff (n : ℕ) :
    dworkCyclotomicBaseChange k p K (PowerSeries.coeff n (dworkArtinHasseExponential k p))
      = PowerSeries.coeff n (dworkArtinHasseExponential K p) := by
  rw [dworkArtinHasseExponential, dworkArtinHasseExponential, PowerSeries.coeff_map,
    PowerSeries.coeff_map]
  exact map_ratCast _ _
theorem dworkCyclotomicBaseChange_dworkArtinHasseEval (x : DworkCyclotomicField k p)
    (hx : ‖x‖ < 1) :
    dworkCyclotomicBaseChange k p K (dworkArtinHasseEval k p x)
      = dworkArtinHasseEval K p (dworkCyclotomicBaseChange k p K x) := by
  have hsum := hasSum_dworkPowerSeriesEval k p (dworkArtinHasseExponential k p) x
    (dworkArtinHasseExponential_coeff_norm_le_one k p) hx
  have hmap := hsum.map (dworkCyclotomicBaseChange k p K).toAddMonoidHom
    (dworkCyclotomicBaseChange_continuous k p K)
  have heq : ∀ n : ℕ,
      ((dworkCyclotomicBaseChange k p K).toAddMonoidHom ∘
        fun n : ℕ => PowerSeries.coeff n (dworkArtinHasseExponential k p) * x ^ n) n
      = PowerSeries.coeff n (dworkArtinHasseExponential K p)
          * (dworkCyclotomicBaseChange k p K x) ^ n := by
    intro n
    show dworkCyclotomicBaseChange k p K
        (PowerSeries.coeff n (dworkArtinHasseExponential k p) * x ^ n) = _
    rw [map_mul, map_pow, dworkCyclotomicBaseChange_dworkArtinHasseExponential_coeff]
  rw [funext heq] at hmap
  rw [dworkArtinHasseEval_eq_tsum K p]
  exact hmap.tsum_eq.symm
@[simp]
theorem dworkCyclotomicBaseChange_dworkArtinHasseParameter :
    dworkCyclotomicBaseChange k p K (dworkArtinHasseParameter k p)
      = dworkArtinHasseParameter K p := by
  refine dworkArtinHasseParameter_unique K p ?_ ?_ ?_
  · rw [norm_dworkCyclotomicBaseChange,
      ← dworkCyclotomicBaseChange_dworkRamificationParameter k p K,
      norm_dworkCyclotomicBaseChange]
    exact (existsUnique_dworkArtinHasseParameter k p).choose_spec.1.1
  · rw [norm_dworkCyclotomicBaseChange]
    exact dworkArtinHasseParameter_norm_lt_one k p
  · rw [← dworkCyclotomicBaseChange_dworkArtinHasseEval k p K _
      (dworkArtinHasseParameter_norm_lt_one k p),
      dworkArtinHasseParameter_spec, dworkCyclotomicBaseChange_dworkPrimitiveRoot]
@[simp]
theorem dworkCyclotomicBaseChange_dworkSplittingFunction_coeff (n : ℕ) :
    dworkCyclotomicBaseChange k p K (PowerSeries.coeff n (dworkSplittingFunction k p))
      = PowerSeries.coeff n (dworkSplittingFunction K p) := by
  rw [dworkSplittingFunction_coeff, dworkSplittingFunction_coeff, map_mul, map_pow,
    dworkCyclotomicBaseChange_dworkArtinHasseParameter,
    dworkCyclotomicBaseChange_dworkArtinHasseExponential_coeff]
theorem coefficientFieldBaseChange_coefficientRingAlgebraMap (a : CoefficientRing k p) :
    coefficientFieldBaseChange k p K (algebraMap k K) (coefficientRingAlgebraMap k p a)
      = coefficientRingAlgebraMap K p
          (coefficientRingBaseChange k p K (algebraMap k K) a) := by
  rw [coefficientRingAlgebraMap, coefficientRingAlgebraMap]
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [coefficientFieldBaseChange_coeRingHom]
  congr 1
  rw [coefficientValuedBaseChange]
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  rw [coefficientFractionFieldBaseChange_algebraMap]
@[simp]
theorem dworkCyclotomicBaseChange_ramifiedTeichmullerLift (a : k) :
    dworkCyclotomicBaseChange k p K (ramifiedTeichmullerLift k p a)
      = ramifiedTeichmullerLift K p (algebraMap k K a) := by
  rw [ramifiedTeichmullerLift, ramifiedTeichmullerLift,
    dworkCyclotomicBaseChange_algebraMap,
    coefficientFieldBaseChange_coefficientRingAlgebraMap]
  congr 2
  rw [coefficientRingBaseChange, teichmullerLift, teichmullerLift]
  exact WittVector.map_teichmuller (p := p) (algebraMap k K) a
end Transport
end FiniteFields.Dwork
end
end
section
noncomputable section
open scoped BigOperators
namespace FiniteFields.Algebra.RootsOfUnity
theorem monomialRootsOfUnity_orthogonality {d : ℕ} {L : Type*} [Field L] {M : ℕ}
    {ζ : L} (hζ : IsPrimitiveRoot ζ M) (v : Fin d →₀ ℕ) :
    ∑ t : Fin d → Fin M, ∏ i, (ζ ^ (t i : ℕ)) ^ (v i)
      = if ∀ i, M ∣ v i then ((M : L)) ^ d else 0 := by
  classical
  have hgeom : ∀ e : ℕ, ∑ j : Fin M, (ζ ^ (j : ℕ)) ^ e
      = if M ∣ e then ((M : L)) else 0 := by
    intro e
    have hcomm : ∀ j : Fin M, (ζ ^ (j : ℕ)) ^ e = (ζ ^ e) ^ (j : ℕ) := by
      intro j
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    simp only [hcomm]
    rw [Fin.sum_univ_eq_sum_range (fun j => (ζ ^ e) ^ j) M]
    by_cases hd : M ∣ e
    · rw [if_pos hd, (hζ.pow_eq_one_iff_dvd e).mpr hd]
      simp
    · rw [if_neg hd]
      have hne : ζ ^ e - 1 ≠ 0 := by
        refine sub_ne_zero.mpr fun hone => hd ?_
        exact (hζ.pow_eq_one_iff_dvd e).mp hone
      have hmul := geom_sum_mul (ζ ^ e) M
      have hxm : (ζ ^ e) ^ M = 1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
      rw [hxm, sub_self] at hmul
      exact (mul_eq_zero.mp hmul).resolve_right hne
  have hprod := Finset.prod_univ_sum (fun _ : Fin d => (Finset.univ : Finset (Fin M)))
    (fun (i : Fin d) (j : Fin M) => (ζ ^ (j : ℕ)) ^ (v i))
  rw [Fintype.piFinset_univ] at hprod
  rw [← hprod]
  simp only [hgeom]
  by_cases hv : ∀ i, M ∣ v i
  · rw [if_pos hv, Finset.prod_congr rfl fun i _ => if_pos (hv i), Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  · rw [if_neg hv]
    obtain ⟨i, hi⟩ := not_forall.mp hv
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
end FiniteFields.Algebra.RootsOfUnity
end
end
section
noncomputable section
open Filter Topology
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
attribute [local instance] FiniteFields.Dwork.dw5cResiduePrimeAlgebra
variable {d : ℕ} (w : PositiveMonomialWeight d)
section Antidiagonal
end Antidiagonal
section Dilation
end Dilation
section Intertwine
theorem exponentDivision_tateDilation_mul (h g : RamifiedOverconvergentTateAlgebra k p w) :
    exponentDivision w p (tateDilation k p w p h * g) = h * exponentDivision w p g := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hvanish : ∀ x : MonomialIndex d × MonomialIndex d,
      (¬ ∃ γ, monomialFrobenius p γ = x.1) →
        overconvergentTateAlgebraCoefficient w x.1 (tateDilation k p w p h) *
          overconvergentTateAlgebraCoefficient w x.2 g = 0 := by
    intro x hx
    rw [tateDilation_coefficient_of_not_dilated k p w p h x.1 hx, zero_mul]
  refine tate_ext k p w fun u => ?_
  rw [exponentDivision_coefficient, coefficient_mul, coefficient_mul,
    sum_antidiagonal_monomialFrobenius hp u _ hvanish]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [tateDilation_coefficient_dilated k p w hp, exponentDivision_coefficient]
@[simp]
theorem ramifiedCoefficientwiseFrobeniusInv_one :
    ramifiedCoefficientwiseFrobeniusInv k p w (1 : RamifiedOverconvergentTateAlgebra k p w)
      = 1 := by
  refine tate_ext k p w fun u => ?_
  rw [ramifiedCoefficientwiseFrobeniusInv_coefficient, coefficient_one]
  split_ifs <;> simp
theorem ramifiedCoefficientwiseFrobeniusInv_mul
    (g h : RamifiedOverconvergentTateAlgebra k p w) :
    ramifiedCoefficientwiseFrobeniusInv k p w (g * h)
      = ramifiedCoefficientwiseFrobeniusInv k p w g
        * ramifiedCoefficientwiseFrobeniusInv k p w h := by
  refine tate_ext k p w fun u => ?_
  rw [ramifiedCoefficientwiseFrobeniusInv_coefficient, coefficient_mul, coefficient_mul,
    map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [map_mul, ramifiedCoefficientwiseFrobeniusInv_coefficient,
    ramifiedCoefficientwiseFrobeniusInv_coefficient]
theorem ramifiedCoefficientwiseFrobeniusInv_iterate_mul (m : ℕ)
    (g h : RamifiedOverconvergentTateAlgebra k p w) :
    (ramifiedCoefficientwiseFrobeniusInv k p w)^[m] (g * h)
      = (ramifiedCoefficientwiseFrobeniusInv k p w)^[m] g
        * (ramifiedCoefficientwiseFrobeniusInv k p w)^[m] h := by
  induction m generalizing g h with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, ramifiedCoefficientwiseFrobeniusInv_mul, ih,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
theorem ramifiedCoefficientwiseFrobeniusInv_exponentDivision
    (g : RamifiedOverconvergentTateAlgebra k p w) :
    ramifiedCoefficientwiseFrobeniusInv k p w (exponentDivision w p g)
      = exponentDivision w p (ramifiedCoefficientwiseFrobeniusInv k p w g) := by
  refine tate_ext k p w fun u => ?_
  rw [ramifiedCoefficientwiseFrobeniusInv_coefficient, exponentDivision_coefficient,
    exponentDivision_coefficient, ramifiedCoefficientwiseFrobeniusInv_coefficient]
theorem ramifiedCoefficientwiseFrobeniusInv_iterate_exponentDivision (m : ℕ)
    (g : RamifiedOverconvergentTateAlgebra k p w) :
    (ramifiedCoefficientwiseFrobeniusInv k p w)^[m] (exponentDivision w p g)
      = exponentDivision w p ((ramifiedCoefficientwiseFrobeniusInv k p w)^[m] g) := by
  induction m generalizing g with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, ramifiedCoefficientwiseFrobeniusInv_exponentDivision,
        ih, Function.iterate_succ_apply]
theorem ramifiedCoefficientwiseFrobeniusInv_iterate_coefficient (m : ℕ)
    (g : RamifiedOverconvergentTateAlgebra k p w) (u : MonomialIndex d) :
    overconvergentTateAlgebraCoefficient w u
        ((ramifiedCoefficientwiseFrobeniusInv k p w)^[m] g)
      = ((ramifiedCoefficientFrobenius k p).symm)^[m]
          (overconvergentTateAlgebraCoefficient w u g) := by
  induction m generalizing g with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, ih,
        ramifiedCoefficientwiseFrobeniusInv_coefficient, Function.iterate_succ_apply]
theorem ramifiedCoefficientwiseFrobeniusInv_iterate_residueDegree
    (g : RamifiedOverconvergentTateAlgebra k p w) :
    (ramifiedCoefficientwiseFrobeniusInv k p w)^[Module.finrank (ZMod p) k] g = g := by
  refine tate_ext k p w fun u => ?_
  rw [ramifiedCoefficientwiseFrobeniusInv_iterate_coefficient,
    ramifiedCoefficientFrobenius_symm_pow_residueDegree]
theorem dworkFrobenius_eq_exponentDivision (f : MonomialIndex d →₀ k)
    (g : RamifiedOverconvergentTateAlgebra k p w) :
    dworkFrobenius k p w f g
      = exponentDivision w p
          (ramifiedCoefficientwiseFrobeniusInv k p w (teichmullerSplittingProduct k p w f)
            * ramifiedCoefficientwiseFrobeniusInv k p w g) := by
  rw [dworkFrobenius, ramifiedCoefficientwiseFrobeniusInv_exponentDivision,
    ramifiedCoefficientwiseFrobeniusInv_mul]
end Intertwine
section Telescope
theorem dworkIteratedSplittingProduct_succ (f : MonomialIndex d →₀ k) (m : ℕ) :
    dworkIteratedSplittingProduct k p w f (m + 1)
      = tateDilation k p w p (dworkIteratedSplittingProduct k p w f m)
        * (ramifiedCoefficientwiseFrobeniusInv k p w)^[m + 1]
            (teichmullerSplittingProduct k p w f) := rfl
theorem dworkFrobenius_iterate_eq (f : MonomialIndex d →₀ k) (m : ℕ)
    (g : RamifiedOverconvergentTateAlgebra k p w) :
    (dworkFrobenius k p w f)^[m] g
      = (exponentDivision w p)^[m]
          (dworkIteratedSplittingProduct k p w f m
            * (ramifiedCoefficientwiseFrobeniusInv k p w)^[m] g) := by
  induction m generalizing g with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, ih, dworkFrobenius_eq_exponentDivision,
        ramifiedCoefficientwiseFrobeniusInv_iterate_exponentDivision,
        ramifiedCoefficientwiseFrobeniusInv_iterate_mul,
        ← Function.iterate_succ_apply (ramifiedCoefficientwiseFrobeniusInv k p w),
        ← Function.iterate_succ_apply (ramifiedCoefficientwiseFrobeniusInv k p w),
        ← exponentDivision_tateDilation_mul,
        ← Function.iterate_succ_apply (exponentDivision w p),
        dworkIteratedSplittingProduct_succ, mul_assoc]
theorem ramifiedCoefficientwiseFrobeniusInv_iterate_residueDegree_mul (s : ℕ)
    (g : RamifiedOverconvergentTateAlgebra k p w) :
    (ramifiedCoefficientwiseFrobeniusInv k p w)^[Module.finrank (ZMod p) k * s] g = g := by
  induction s generalizing g with
  | zero => simp
  | succ s ih =>
      rw [Nat.mul_succ, Function.iterate_add_apply,
        ramifiedCoefficientwiseFrobeniusInv_iterate_residueDegree, ih]
theorem dworkQFrobenius_iterate_eq (f : MonomialIndex d →₀ k) (s : ℕ)
    (g : RamifiedOverconvergentTateAlgebra k p w) :
    (dworkQFrobenius k p w f)^[s] g
      = (exponentDivision w p)^[Module.finrank (ZMod p) k * s]
          (dworkIteratedSplittingProduct k p w f (Module.finrank (ZMod p) k * s) * g) := by
  have hiter : (dworkQFrobenius k p w f)^[s] g
      = (dworkFrobenius k p w f)^[Module.finrank (ZMod p) k * s] g := by
    rw [Function.iterate_mul]
    rfl
  rw [hiter, dworkFrobenius_iterate_eq,
    ramifiedCoefficientwiseFrobeniusInv_iterate_residueDegree_mul]
end Telescope
section ExponentDivisionKernel
theorem exponentDivision_iterate_coefficient (n : ℕ)
    (g : RamifiedOverconvergentTateAlgebra k p w) (u : MonomialIndex d) :
    overconvergentTateAlgebraCoefficient w u ((exponentDivision w p)^[n] g)
      = overconvergentTateAlgebraCoefficient w (monomialFrobenius (p ^ n) u) g := by
  induction n generalizing g u with
  | zero => simp [monomialFrobenius]
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih, exponentDivision_coefficient]
      congr 1
      simp only [monomialFrobenius, smul_smul]
      rw [pow_succ']
omit [Finite k] in
private theorem monomialFrobenius_le (m : ℕ) (hm : m ≠ 0) (u : MonomialIndex d) :
    u ≤ monomialFrobenius m u := by
  intro i
  simp only [monomialFrobenius_apply]
  exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hm)
theorem coefficient_mul_unitMonomial (h : RamifiedOverconvergentTateAlgebra k p w)
    (v u : MonomialIndex d) :
    overconvergentTateAlgebraCoefficient w u (h * unitMonomial k p w v)
      = if v ≤ u then overconvergentTateAlgebraCoefficient w (u - v) h else 0 := by
  classical
  rw [coefficient_mul]
  simp only [unitMonomial_coefficient]
  by_cases hv : v ≤ u
  · rw [if_pos hv, Finset.sum_eq_single (u - v, v)]
    · rw [if_pos rfl, mul_one]
    · rintro ⟨a, b⟩ hab hne
      have hsum : a + b = u := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
      by_cases hb : b = v
      · exfalso
        apply hne
        subst hb
        have ha : a = u - b := by
          rw [← hsum]
          simp
        rw [ha]
      · rw [if_neg hb, mul_zero]
    · intro hmem
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (tsub_add_cancel_of_le hv)) hmem
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hsum : x.1 + x.2 = u := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have hne : x.2 ≠ v := by
      rintro rfl
      exact hv (by rw [← hsum]; exact le_add_self)
    rw [if_neg hne, mul_zero]
omit [Finite k] in
private theorem monomialFrobenius_sub_self {P : ℕ} (hP : P ≠ 0) (u : MonomialIndex d) :
    monomialFrobenius P u - u = monomialFrobenius (P - 1) u := by
  ext i
  simp only [Finsupp.tsub_apply, monomialFrobenius_apply]
  cases P with
  | zero => exact absurd rfl hP
  | succ P =>
      simp only [Nat.add_sub_cancel, Nat.succ_mul]
end ExponentDivisionKernel
section IteratedKernel
omit [Finite k] in
theorem dworkQPow_ne_zero (s : ℕ) : dworkQPow k p s ≠ 0 :=
  pow_ne_zero _ (Fact.out : p.Prime).ne_zero
theorem dworkQFrobeniusIteratedKernel_one (f : MonomialIndex d →₀ k) :
    dworkQFrobeniusIteratedKernel k p w f 1 = dworkQFrobeniusKernel k p w f := rfl
theorem dworkQFrobeniusIteratedKernel_eq (f : MonomialIndex d →₀ k) (s : ℕ)
    (u v : MonomialIndex d) :
    dworkQFrobeniusIteratedKernel k p w f s u v
      = if v ≤ monomialFrobenius (dworkQPow k p s) u then
          overconvergentTateAlgebraCoefficient w
            (monomialFrobenius (dworkQPow k p s) u - v)
            (dworkIteratedSplittingProduct k p w f (Module.finrank (ZMod p) k * s))
        else 0 := by
  rw [dworkQFrobeniusIteratedKernel, dworkQFrobenius_iterate_eq,
    exponentDivision_iterate_coefficient, coefficient_mul_unitMonomial]
  rfl
theorem dworkQFrobeniusIteratedKernel_diagonal (f : MonomialIndex d →₀ k) (s : ℕ)
    (u : MonomialIndex d) :
    dworkQFrobeniusIteratedKernel k p w f s u u
      = overconvergentTateAlgebraCoefficient w
          (monomialFrobenius (dworkQPow k p s - 1) u)
          (dworkIteratedSplittingProduct k p w f (Module.finrank (ZMod p) k * s)) := by
  rw [dworkQFrobeniusIteratedKernel_eq,
    if_pos (monomialFrobenius_le _ (dworkQPow_ne_zero k p s) u),
    monomialFrobenius_sub_self (dworkQPow_ne_zero k p s)]
end IteratedKernel
section FiniteTrace
omit [Fact p.Prime] [Field k] [CharP k p] [Finite k] in
private theorem exists_monomialFrobenius_iff {M : ℕ} (v : MonomialIndex d) :
    (∃ u, monomialFrobenius M u = v) ↔ ∀ i, M ∣ v i := by
  constructor
  · rintro ⟨u, rfl⟩ i
    exact ⟨u i, monomialFrobenius_apply M u i⟩
  · intro h
    refine ⟨Finsupp.mapRange (fun x => x / M) (by simp) v, ?_⟩
    ext i
    simp only [monomialFrobenius_apply, Finsupp.mapRange_apply]
    exact Nat.mul_div_cancel' (h i)
theorem monomialRootsOfUnity_orthogonality {L : Type*} [Field L] {M : ℕ}
    {ζ : L} (hζ : IsPrimitiveRoot ζ M) (v : MonomialIndex d) :
    ∑ t : Fin d → Fin M, ∏ i, (ζ ^ (t i : ℕ)) ^ (v i)
      = if ∀ i, M ∣ v i then ((M : L)) ^ d else 0 := by
  exact FiniteFields.Algebra.RootsOfUnity.monomialRootsOfUnity_orthogonality hζ v
theorem coefficient_finsuppToOverconvergentTateAlgebra
    (a : MonomialIndex d →₀ DworkCyclotomicField k p) (v : MonomialIndex d) :
    overconvergentTateAlgebraCoefficient w v
        (finsuppToOverconvergentTateAlgebra w (1 : DworkCyclotomicField k p) a) = a v := by
  simp [overconvergentTateAlgebraCoefficient_apply, seriesCoefficient_apply]
end FiniteTrace
section CutoffTracePower
omit [Fact p.Prime] [Field k] [CharP k p] [Finite k] in
private theorem monomialWeight_mono {u v : MonomialIndex d} (h : v ≤ u) :
    monomialWeight w v ≤ monomialWeight w u := by
  conv_rhs => rw [← add_tsub_cancel_of_le h]
  rw [monomialWeight_add]
  exact Nat.le_add_right _ _
omit [Finite k] in
@[simp]
theorem dworkQPow_one : dworkQPow k p 1 = p ^ Module.finrank (ZMod p) k := by
  rw [dworkQPow, mul_one]
omit [Finite k] in
theorem dworkQPow_succ (s : ℕ) :
    dworkQPow k p (s + 1) = dworkQPow k p s * dworkQPow k p 1 := by
  rw [dworkQPow, dworkQPow, dworkQPow, ← pow_add]
  congr 1
  ring
omit [Finite k] in
theorem dworkQPow_one_le_succ (s : ℕ) : dworkQPow k p 1 ≤ dworkQPow k p (s + 1) := by
  rw [dworkQPow, dworkQPow]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos
    (Nat.mul_le_mul_left _ (by omega))
theorem dworkQFrobenius_coefficient (f : MonomialIndex d →₀ k)
    (g : RamifiedOverconvergentTateAlgebra k p w) (u : MonomialIndex d) :
    overconvergentTateAlgebraCoefficient w u (dworkQFrobenius k p w f g)
      = ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal (monomialFrobenius (dworkQPow k p 1) u),
          overconvergentTateAlgebraCoefficient w ab.1
              (dworkIteratedSplittingProduct k p w f (Module.finrank (ZMod p) k))
            * overconvergentTateAlgebraCoefficient w ab.2 g := by
  have h := dworkQFrobenius_iterate_eq k p w f 1 g
  rw [Function.iterate_one, mul_one] at h
  rw [h, exponentDivision_iterate_coefficient, coefficient_mul, dworkQPow_one]
theorem dworkQFrobeniusKernel_eq_coefficient (f : MonomialIndex d →₀ k)
    (u v : MonomialIndex d) :
    dworkQFrobeniusKernel k p w f u v
      = if v ≤ monomialFrobenius (dworkQPow k p 1) u then
          overconvergentTateAlgebraCoefficient w
            (monomialFrobenius (dworkQPow k p 1) u - v)
            (dworkIteratedSplittingProduct k p w f (Module.finrank (ZMod p) k))
        else 0 := by
  have h := dworkQFrobeniusIteratedKernel_eq k p w f 1 u v
  rw [dworkQFrobeniusIteratedKernel_one] at h
  rw [h, mul_one]
theorem dworkQFrobeniusKernel_eq_zero_of_not_le (f : MonomialIndex d →₀ k)
    {u v : MonomialIndex d} (h : ¬ v ≤ monomialFrobenius (dworkQPow k p 1) u) :
    dworkQFrobeniusKernel k p w f u v = 0 := by
  rw [dworkQFrobeniusKernel_eq_coefficient, if_neg h]
theorem dworkQFrobeniusIteratedKernel_succ (f : MonomialIndex d →₀ k) (s : ℕ)
    (u v : MonomialIndex d) :
    dworkQFrobeniusIteratedKernel k p w f (s + 1) u v
      = ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal (monomialFrobenius (dworkQPow k p 1) u),
          dworkQFrobeniusKernel k p w f u ab.2
            * dworkQFrobeniusIteratedKernel k p w f s ab.2 v := by
  classical
  rw [dworkQFrobeniusIteratedKernel, Function.iterate_succ_apply',
    dworkQFrobenius_coefficient]
  refine Finset.sum_congr rfl fun ab hab => ?_
  have hsum : ab.1 + ab.2 = monomialFrobenius (dworkQPow k p 1) u :=
    Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  have hle : ab.2 ≤ monomialFrobenius (dworkQPow k p 1) u := by
    rw [← hsum]
    exact le_add_self
  have hfirst : ab.1 = monomialFrobenius (dworkQPow k p 1) u - ab.2 := by
    rw [← hsum]
    simp
  rw [dworkQFrobeniusKernel_eq_coefficient, if_pos hle, hfirst]
  rfl
private theorem sum_box_eq_sum_cutoff (f : MonomialIndex d →₀ k) (u : MonomialIndex d)
    (bound : ℕ) (hu : dworkQPow k p 1 * monomialWeight w u ≤ bound)
    (c : MonomialIndex d → DworkCyclotomicField k p) :
    ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal (monomialFrobenius (dworkQPow k p 1) u),
        dworkQFrobeniusKernel k p w f u ab.2 * c ab.2
      = ∑ x : WeightedCutoff w bound, dworkQFrobeniusKernel k p w f u x.1 * c x.1 := by
  classical
  set Q : ℕ := dworkQPow k p 1 with hQ
  set B : Finset (MonomialIndex d) :=
    (Finset.HasAntidiagonal.antidiagonal (monomialFrobenius Q u)).image Prod.snd with hB
  set C : Finset (MonomialIndex d) :=
    (Finset.univ : Finset (WeightedCutoff w bound)).image Subtype.val with hC
  have hBinj : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal (monomialFrobenius Q u),
      ∀ y ∈ Finset.HasAntidiagonal.antidiagonal (monomialFrobenius Q u), x.2 = y.2 → x = y := by
    intro x hx y hy hxy
    have hx' : x.1 + x.2 = monomialFrobenius Q u := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have hy' : y.1 + y.2 = monomialFrobenius Q u := Finset.HasAntidiagonal.mem_antidiagonal.mp hy
    refine Prod.ext ?_ hxy
    rw [hxy] at hx'
    exact add_right_cancel (hx'.trans hy'.symm)
  have hCinj : ∀ x ∈ (Finset.univ : Finset (WeightedCutoff w bound)),
      ∀ y ∈ (Finset.univ : Finset (WeightedCutoff w bound)),
      (x : MonomialIndex d) = (y : MonomialIndex d) → x = y := by
    intro x _ y _ hxy
    exact Subtype.ext hxy
  have hleft : ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal (monomialFrobenius Q u),
      dworkQFrobeniusKernel k p w f u ab.2 * c ab.2
      = ∑ β ∈ B, dworkQFrobeniusKernel k p w f u β * c β := by
    rw [hB]
    exact (Finset.sum_image (f := fun β => dworkQFrobeniusKernel k p w f u β * c β)
      hBinj).symm
  have hright : ∑ x : WeightedCutoff w bound,
      dworkQFrobeniusKernel k p w f u x.1 * c x.1
      = ∑ β ∈ C, dworkQFrobeniusKernel k p w f u β * c β := by
    rw [hC]
    exact (Finset.sum_image (f := fun β => dworkQFrobeniusKernel k p w f u β * c β)
      hCinj).symm
  have hsubset : B ⊆ C := by
    intro β hβ
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hβ
    have hle : ab.2 ≤ monomialFrobenius Q u := by
      rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hab]
      exact le_add_self
    refine Finset.mem_image.mpr ⟨⟨ab.2, ?_⟩, Finset.mem_univ _, rfl⟩
    have hwt : monomialWeight w ab.2 ≤ monomialWeight w (monomialFrobenius Q u) :=
      monomialWeight_mono w hle
    rw [monomialWeight_monomialFrobenius] at hwt
    exact hwt.trans hu
  have hzero : ∀ β ∈ C, β ∉ B → dworkQFrobeniusKernel k p w f u β * c β = 0 := by
    intro β _ hβ
    have hnot : ¬ β ≤ monomialFrobenius Q u := by
      intro hle
      exact hβ (Finset.mem_image.mpr
        ⟨(monomialFrobenius Q u - β, β),
          Finset.HasAntidiagonal.mem_antidiagonal.mpr (tsub_add_cancel_of_le hle), rfl⟩)
    rw [dworkQFrobeniusKernel_eq_zero_of_not_le k p w f hnot, zero_mul]
  rw [hleft, hright, Finset.sum_subset hsubset hzero]
theorem cutoffKernel_pow_apply_eq_iteratedKernel (f : MonomialIndex d →₀ k)
    (bound s : ℕ) (u v : WeightedCutoff w bound)
    (hu : dworkQPow k p s * monomialWeight w u.1 ≤ bound) :
    ((cutoffKernel w (dworkQFrobeniusKernel k p w f) bound) ^ s) u v
      = dworkQFrobeniusIteratedKernel k p w f s u.1 v.1 := by
  classical
  induction s generalizing u with
  | zero =>
      rw [pow_zero, Matrix.one_apply, dworkQFrobeniusIteratedKernel,
        Function.iterate_zero_apply, unitMonomial_coefficient]
      by_cases huv : u = v
      · rw [if_pos huv, if_pos (congrArg Subtype.val huv)]
      · rw [if_neg huv, if_neg (fun h => huv (Subtype.ext h))]
  | succ s ih =>
      have hsucc : dworkQPow k p (s + 1) = dworkQPow k p s * dworkQPow k p 1 :=
        dworkQPow_succ k p s
      have hstep : dworkQPow k p 1 * monomialWeight w u.1 ≤ bound :=
        le_trans (Nat.mul_le_mul_right _ (dworkQPow_one_le_succ k p s)) hu
      rw [pow_succ', Matrix.mul_apply]
      have hterm : ∀ x : WeightedCutoff w bound,
          cutoffKernel w (dworkQFrobeniusKernel k p w f) bound u x
              * ((cutoffKernel w (dworkQFrobeniusKernel k p w f) bound) ^ s) x v
            = dworkQFrobeniusKernel k p w f u.1 x.1
                * dworkQFrobeniusIteratedKernel k p w f s x.1 v.1 := by
        intro x
        rw [cutoffKernel_apply]
        by_cases hx : dworkQFrobeniusKernel k p w f u.1 x.1 = 0
        · rw [hx, zero_mul, zero_mul]
        · have hbox : x.1 ≤ monomialFrobenius (dworkQPow k p 1) u.1 := by
            by_contra hcon
            exact hx (dworkQFrobeniusKernel_eq_zero_of_not_le k p w f hcon)
          have hwt : dworkQPow k p s * monomialWeight w x.1 ≤ bound := by
            have hle : monomialWeight w x.1
                ≤ dworkQPow k p 1 * monomialWeight w u.1 := by
              have := monomialWeight_mono w hbox
              rwa [monomialWeight_monomialFrobenius] at this
            calc dworkQPow k p s * monomialWeight w x.1
                ≤ dworkQPow k p s * (dworkQPow k p 1 * monomialWeight w u.1) :=
                  Nat.mul_le_mul_left _ hle
              _ = dworkQPow k p (s + 1) * monomialWeight w u.1 := by
                  rw [hsucc]; ring
              _ ≤ bound := hu
          rw [ih x hwt]
      rw [Finset.sum_congr rfl fun x _ => hterm x,
        ← sum_box_eq_sum_cutoff k p w f u.1 bound hstep
          (fun β => dworkQFrobeniusIteratedKernel k p w f s β v.1),
        dworkQFrobeniusIteratedKernel_succ]
theorem dworkCutoffTracePower_eq_splittingSum (f : MonomialIndex d →₀ k)
    (bound s : ℕ) (u : WeightedCutoff w bound)
    (hu : dworkQPow k p s * monomialWeight w u.1 ≤ bound) :
    ((cutoffKernel w (dworkQFrobeniusKernel k p w f) bound) ^ s) u u
      = overconvergentTateAlgebraCoefficient w
          (monomialFrobenius (dworkQPow k p s - 1) u.1)
          (dworkIteratedSplittingProduct k p w f (Module.finrank (ZMod p) k * s)) := by
  rw [cutoffKernel_pow_apply_eq_iteratedKernel k p w f bound s u u hu,
    dworkQFrobeniusIteratedKernel_diagonal]
end CutoffTracePower
section TraceLimit
private theorem mem_monomialCutoffFinset (bound : ℕ) (v : MonomialIndex d) :
    v ∈ monomialCutoffFinset w bound ↔ monomialWeight w v ≤ bound := by
  constructor
  · intro hv
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hv
    exact u.2
  · intro hv
    exact Finset.mem_image.mpr ⟨⟨v, hv⟩, Finset.mem_univ _, rfl⟩
private theorem sum_weightedCutoff_eq_sum_finset (bound : ℕ)
    (g : MonomialIndex d → DworkCyclotomicField k p) :
    ∑ u : WeightedCutoff w bound, g u.1 = ∑ v ∈ monomialCutoffFinset w bound, g v := by
  refine (Finset.sum_image ?_).symm
  intro x _ y _ hxy
  exact Subtype.ext hxy
private theorem monomialCutoffFinset_subset {smaller larger : ℕ} (h : smaller ≤ larger) :
    monomialCutoffFinset w smaller ⊆ monomialCutoffFinset w larger := by
  intro v hv
  exact (mem_monomialCutoffFinset w larger v).mpr
    (((mem_monomialCutoffFinset w smaller v).mp hv).trans h)
private theorem tendsto_monomialCutoffFinset :
    Tendsto (monomialCutoffFinset w) atTop atTop := by
  refine Filter.tendsto_atTop.mpr fun t => ?_
  filter_upwards [Filter.eventually_ge_atTop (t.sup (monomialWeight w))] with bound hbound
  intro v hv
  exact (mem_monomialCutoffFinset w bound v).mpr
    ((Finset.le_sup (f := monomialWeight w) hv).trans hbound)
private theorem tendsto_sum_monomialCutoffFinset
    {g : MonomialIndex d → DworkCyclotomicField k p} {S : DworkCyclotomicField k p}
    (hS : HasSum g S) :
    Tendsto (fun bound => ∑ v ∈ monomialCutoffFinset w bound, g v) atTop (nhds S) :=
  hS.comp (tendsto_monomialCutoffFinset w)
private theorem cutoffPowerDiagonal_apply (f : MonomialIndex d →₀ k) (s bound : ℕ)
    (v : MonomialIndex d) (hv : monomialWeight w v ≤ bound) :
    cutoffPowerDiagonal k p w f s bound v
      = ((cutoffKernel w (dworkQFrobeniusKernel k p w f) bound) ^ s) ⟨v, hv⟩ ⟨v, hv⟩ := by
  rw [cutoffPowerDiagonal, dif_pos hv]
section MatrixBounds
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem norm_matrix_pow_entry_le_one
    (A : Matrix ι ι (DworkCyclotomicField k p)) (hA : ∀ i j, ‖A i j‖ ≤ 1) (n : ℕ) (i j : ι) :
    ‖(A ^ n) i j‖ ≤ 1 := by
  induction n generalizing i j with
  | zero =>
      rw [pow_zero, Matrix.one_apply]
      split_ifs <;> simp
  | succ n ih =>
      rw [pow_succ, Matrix.mul_apply]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
      rw [norm_mul]
      exact mul_le_one₀ (ih i x) (norm_nonneg _) (hA x j)
private theorem norm_matrix_pow_entry_le_of_row
    (A : Matrix ι ι (DworkCyclotomicField k p)) (hA : ∀ i j, ‖A i j‖ ≤ 1)
    {c : ℝ} (hc : 0 ≤ c) (i : ι) (hrow : ∀ j, ‖A i j‖ ≤ c) (n : ℕ) (j : ι) :
    ‖(A ^ (n + 1)) i j‖ ≤ c := by
  rw [pow_succ', Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hc fun x _ => ?_
  rw [norm_mul]
  calc ‖A i x‖ * ‖(A ^ n) x j‖ ≤ c * 1 :=
        mul_le_mul (hrow x) (norm_matrix_pow_entry_le_one k p A hA n x j)
          (norm_nonneg _) hc
    _ = c := mul_one c
end MatrixBounds
theorem two_le_dworkQPow {s : ℕ} (hs : 0 < s) : 2 ≤ dworkQPow k p s := by
  refine le_trans (two_le_qCard k p) ?_
  rw [dworkQPow]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos
    (Nat.le_mul_of_pos_right _ hs)
theorem summable_dworkSplittingDiagonal (f : MonomialIndex d →₀ k) {s : ℕ} (hs : 0 < s) :
    Summable (dworkSplittingDiagonal k p w f s) := by
  have hQ : 2 ≤ dworkQPow k p s := two_le_dworkQPow k p hs
  have hray : Function.Injective
      (fun u : MonomialIndex d => monomialFrobenius (dworkQPow k p s - 1) u) :=
    monomialFrobenius_injective _ (by omega)
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  have hzero := zero_at_infty
    ((dworkIteratedSplittingProduct k p w f (Module.finrank (ZMod p) k * s)).toSeries)
  rw [Filter.cocompact_eq_cofinite] at hzero
  have hcomp : Tendsto (fun u : MonomialIndex d =>
      dw5cDiscreteMonomial (monomialFrobenius (dworkQPow k p s - 1) u)) cofinite cofinite :=
    ((dw5cDiscreteMonomial_injective (d := d)).comp hray).tendsto_cofinite
  exact hzero.comp hcomp
theorem norm_finiteKernelPowerTrace_sub_splittingSum_le (f : MonomialIndex d →₀ k)
    {s : ℕ} (hs : 0 < s) (bound : ℕ) :
    ‖finiteKernelPowerTrace w (dworkQFrobeniusKernel k p w f) s bound
        - ∑ v ∈ monomialCutoffFinset w (bound / dworkQPow k p s),
            dworkSplittingDiagonal k p w f s v‖
      ≤ dworkQFrobeniusTailBound k p w f (bound / dworkQPow k p s) := by
  set Q : ℕ := dworkQPow k p s with hQdef
  have hQpos : 0 < Q := Nat.pos_of_ne_zero (dworkQPow_ne_zero k p s)
  set level : ℕ := bound / Q with hlevel
  have hlevel_le : Q * level ≤ bound := by
    rw [hlevel, Nat.mul_comm]
    exact Nat.div_mul_le_self bound Q
  have hlevel_bound : level ≤ bound :=
    le_trans (Nat.le_mul_of_pos_left _ hQpos) hlevel_le
  have htrace : finiteKernelPowerTrace w (dworkQFrobeniusKernel k p w f) s bound
      = ∑ v ∈ monomialCutoffFinset w bound, cutoffPowerDiagonal k p w f s bound v := by
    rw [finiteKernelPowerTrace, Matrix.trace, ← sum_weightedCutoff_eq_sum_finset]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Matrix.diag_apply, cutoffPowerDiagonal_apply k p w f s bound u.1 u.2]
  have hexact : ∀ v ∈ monomialCutoffFinset w level,
      cutoffPowerDiagonal k p w f s bound v = dworkSplittingDiagonal k p w f s v := by
    intro v hv
    have hwt : monomialWeight w v ≤ level := (mem_monomialCutoffFinset w level v).mp hv
    have hvb : monomialWeight w v ≤ bound := hwt.trans hlevel_bound
    rw [cutoffPowerDiagonal_apply k p w f s bound v hvb, dworkSplittingDiagonal,
      dworkCutoffTracePower_eq_splittingSum k p w f bound s ⟨v, hvb⟩
        (le_trans (Nat.mul_le_mul_left _ hwt) hlevel_le)]
  have hdecay := dworkQFrobeniusKernel_decay k p w f
  have htail : ∀ v ∈ monomialCutoffFinset w bound, v ∉ monomialCutoffFinset w level →
      ‖cutoffPowerDiagonal k p w f s bound v‖ ≤ dworkQFrobeniusTailBound k p w f level := by
    intro v hv hnot
    have hvb : monomialWeight w v ≤ bound := (mem_monomialCutoffFinset w bound v).mp hv
    have hgt : level < monomialWeight w v := by
      by_contra hcon
      exact hnot ((mem_monomialCutoffFinset w level v).mpr (Nat.le_of_not_lt hcon))
    obtain ⟨s', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
    have hall : ∀ i j : WeightedCutoff w bound,
        ‖cutoffKernel w (dworkQFrobeniusNormalizedKernel k p w f) bound i j‖ ≤ 1 := by
      intro i j
      rw [cutoffKernel_apply]
      exact hdecay.2 i.1 j.1
    have hrow : ∀ j : WeightedCutoff w bound,
        ‖cutoffKernel w (dworkQFrobeniusNormalizedKernel k p w f) bound ⟨v, hvb⟩ j‖
          ≤ dworkQFrobeniusTailBound k p w f level := by
      intro j
      rw [cutoffKernel_apply]
      exact hdecay.1.2.2 level v j.1 (Or.inl hgt)
    rw [cutoffPowerDiagonal_apply k p w f _ bound v hvb,
      ← cutoffKernel_dworkQFrobeniusNormalizedKernel_pow_diagonal k p w f bound (s' + 1)]
    exact norm_matrix_pow_entry_le_of_row k p
      (cutoffKernel w (dworkQFrobeniusNormalizedKernel k p w f) bound) hall
      (dworkQFrobeniusTailBound_nonneg k p w f level) ⟨v, hvb⟩ hrow s' ⟨v, hvb⟩
  calc ‖finiteKernelPowerTrace w (dworkQFrobeniusKernel k p w f) s bound
        - ∑ v ∈ monomialCutoffFinset w level, dworkSplittingDiagonal k p w f s v‖
      = ‖∑ v ∈ monomialCutoffFinset w bound \ monomialCutoffFinset w level,
          cutoffPowerDiagonal k p w f s bound v‖ := by
        rw [Finset.sum_sdiff_eq_sub (monomialCutoffFinset_subset w hlevel_bound), htrace,
          Finset.sum_congr rfl hexact]
    _ ≤ dworkQFrobeniusTailBound k p w f level := by
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
          (dworkQFrobeniusTailBound_nonneg k p w f level) fun v hv => ?_
        exact htail v (Finset.mem_sdiff.mp hv).1 (Finset.mem_sdiff.mp hv).2
private theorem tendsto_div_atTop {Q : ℕ} (hQ : 0 < Q) :
    Tendsto (fun bound : ℕ => bound / Q) atTop atTop := by
  refine Filter.tendsto_atTop_atTop.mpr fun N => ⟨N * Q, fun b hb => ?_⟩
  exact (Nat.le_div_iff_mul_le hQ).mpr hb
theorem dworkTracePower_eq_splittingSum (f : MonomialIndex d →₀ k) (s : ℕ+) :
    NuclearOperator.tracePower w (dworkQFrobeniusNuclearOperator k p w f) s
      = ∑' u : MonomialIndex d, dworkSplittingDiagonal k p w f (s : ℕ) u := by
  have hs : 0 < (s : ℕ) := s.2
  have hQpos : 0 < dworkQPow k p (s : ℕ) := Nat.pos_of_ne_zero (dworkQPow_ne_zero k p _)
  have hsum := (summable_dworkSplittingDiagonal k p w f hs).hasSum
  have hpartial : Tendsto (fun bound : ℕ =>
      ∑ v ∈ monomialCutoffFinset w (bound / dworkQPow k p (s : ℕ)),
        dworkSplittingDiagonal k p w f (s : ℕ) v) atTop
      (nhds (∑' u : MonomialIndex d, dworkSplittingDiagonal k p w f (s : ℕ) u)) :=
    (tendsto_sum_monomialCutoffFinset k p w hsum).comp (tendsto_div_atTop hQpos)
  have hclose : Tendsto (fun bound : ℕ =>
      finiteKernelPowerTrace w (dworkQFrobeniusKernel k p w f) (s : ℕ) bound
        - ∑ v ∈ monomialCutoffFinset w (bound / dworkQPow k p (s : ℕ)),
            dworkSplittingDiagonal k p w f (s : ℕ) v) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun bound => norm_nonneg _)
      (fun bound => norm_finiteKernelPowerTrace_sub_splittingSum_le k p w f hs bound) ?_
    exact (dworkQFrobeniusTailBound_tendsto k p w f).comp (tendsto_div_atTop hQpos)
  have hmain : Tendsto (fun bound : ℕ =>
      finiteKernelPowerTrace w (dworkQFrobeniusKernel k p w f) (s : ℕ) bound) atTop
      (nhds (∑' u : MonomialIndex d, dworkSplittingDiagonal k p w f (s : ℕ) u)) := by
    have := hclose.add hpartial
    rw [zero_add] at this
    refine this.congr fun bound => ?_
    ring
  exact tendsto_nhds_unique
    (tracePower_dworkQFrobeniusNuclearOperator_tendsto k p w f s) hmain
end TraceLimit
section Evaluation
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
omit [CompleteSpace K] in
@[simp]
theorem coefficient_one' (u : MonomialIndex d) :
    overconvergentTateAlgebraCoefficient w u (1 : OverconvergentTateAlgebra K d w)
      = if u = 0 then 1 else 0 := by
  change seriesCoefficient w u (overconvergentSeriesOne w) = _
  rw [overconvergentSeriesOne, seriesCoefficient_apply, finsuppToOverconvergentSeries_apply]
  simp [Finsupp.single_apply, eq_comm]
omit [CompleteSpace K] in
theorem coefficient_mul' (g h : OverconvergentTateAlgebra K d w) (u : MonomialIndex d) :
    overconvergentTateAlgebraCoefficient w u (g * h)
      = ∑ xy ∈ Finset.HasAntidiagonal.antidiagonal u,
          overconvergentTateAlgebraCoefficient w xy.1 g *
            overconvergentTateAlgebraCoefficient w xy.2 h := by
  have hconvolution := seriesConvolution_weightedCoefficient w (1 : K) g.toSeries h.toSeries u
  simpa [seriesConvolution, weightedCoefficient_apply,
    overconvergentTateAlgebraCoefficient_apply, seriesCoefficient_apply] using hconvolution
omit [CompleteSpace K] in
@[simp]
theorem tateEval_one (x : Fin d → K) :
    tateEval w (1 : OverconvergentTateAlgebra K d w) x = 1 := by
  rw [tateEval]
  have hterm : ∀ u : MonomialIndex d,
      tateEvalTerm w (1 : OverconvergentTateAlgebra K d w) x u = if u = 0 then 1 else 0 := by
    intro u
    rw [tateEvalTerm, coefficient_one']
    by_cases hu : u = 0
    · subst hu
      simp
    · rw [if_neg hu, zero_mul]
  rw [tsum_congr hterm, tsum_ite_eq]
theorem tateEval_mul {x : Fin d → K} (hx : ∀ i, ‖x i‖ = 1)
    (g h : OverconvergentTateAlgebra K d w) :
    tateEval w (g * h) x = tateEval w g x * tateEval w h x := by
  have hg := summable_tateEvalTerm w g hx
  have hh := summable_tateEvalTerm w h hx
  have hgh : Summable (fun z : MonomialIndex d × MonomialIndex d =>
      tateEvalTerm w g x z.1 * tateEvalTerm w h x z.2) := hg.mul_of_nonarchimedean hh
  rw [tateEval, tateEval, tateEval, hg.tsum_mul_tsum_eq_tsum_sum_antidiagonal hh hgh]
  refine tsum_congr fun u => ?_
  rw [tateEvalTerm, coefficient_mul' w g h u, Finset.sum_mul]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hz' : z.1 + z.2 = u := Finset.HasAntidiagonal.mem_antidiagonal.mp hz
  rw [tateEvalTerm, tateEvalTerm, ← hz']
  have hsplit : ∏ i, x i ^ (z.1 + z.2) i = (∏ i, x i ^ z.1 i) * ∏ i, x i ^ z.2 i := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [Finsupp.add_apply, pow_add]
  rw [hsplit]
  ring
theorem tateEval_prod {ι : Type*} {x : Fin d → K} (hx : ∀ i, ‖x i‖ = 1)
    (t : Finset ι) (F : ι → OverconvergentTateAlgebra K d w) :
    tateEval w (∏ i ∈ t, F i) x = ∏ i ∈ t, tateEval w (F i) x := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, tateEval_mul w hx, ih]
omit [IsUltrametricDist K] [CompleteSpace K] in
theorem norm_eq_one_of_isPrimitiveRoot {M : ℕ} (hM : M ≠ 0) {ζ : K} (hζ : IsPrimitiveRoot ζ M)
    (j : ℕ) : ‖ζ ^ j‖ = 1 := by
  have hpow : ‖ζ‖ ^ M = 1 := by
    rw [← norm_pow, hζ.pow_eq_one, norm_one]
  have hone : ‖ζ‖ = 1 := by
    rcases lt_trichotomy ‖ζ‖ 1 with hlt | heq | hgt
    · exact absurd hpow (pow_lt_one₀ (norm_nonneg ζ) hlt hM).ne
    · exact heq
    · exact absurd hpow (one_lt_pow₀ hgt hM).ne'
  rw [norm_pow, hone, one_pow]
theorem sum_rootsOfUnity_tateEval {M : ℕ} (hM : M ≠ 0) {ζ : K} (hζ : IsPrimitiveRoot ζ M)
    (g : OverconvergentTateAlgebra K d w) :
    ∑ t : Fin d → Fin M, tateEval w g (fun i => ζ ^ (t i : ℕ))
      = (M : K) ^ d * ∑' u : MonomialIndex d,
          overconvergentTateAlgebraCoefficient w (monomialFrobenius M u) g := by
  classical
  have hx : ∀ t : Fin d → Fin M, ∀ i, ‖(ζ ^ (t i : ℕ) : K)‖ = 1 := fun t i =>
    norm_eq_one_of_isPrimitiveRoot hM hζ _
  have hswap : ∑ t : Fin d → Fin M, tateEval w g (fun i => ζ ^ (t i : ℕ))
      = ∑' u : MonomialIndex d,
          ∑ t : Fin d → Fin M, tateEvalTerm w g (fun i => ζ ^ (t i : ℕ)) u :=
    (Summable.tsum_finsetSum fun t _ => summable_tateEvalTerm w g (hx t)).symm
  have hinner : ∀ u : MonomialIndex d,
      ∑ t : Fin d → Fin M, tateEvalTerm w g (fun i => ζ ^ (t i : ℕ)) u
        = overconvergentTateAlgebraCoefficient w u g
            * (if ∀ i, M ∣ u i then (M : K) ^ d else 0) := by
    intro u
    rw [← monomialRootsOfUnity_orthogonality hζ u, Finset.mul_sum]
    rfl
  have hsupport : Function.support (fun u : MonomialIndex d =>
      overconvergentTateAlgebraCoefficient w u g
        * (if ∀ i, M ∣ u i then (M : K) ^ d else 0))
      ⊆ Set.range (monomialFrobenius (d := d) M) := by
    intro u hu
    by_cases hdvd : ∀ i, M ∣ u i
    · obtain ⟨v, hv⟩ := (exists_monomialFrobenius_iff u).mpr hdvd
      exact ⟨v, hv⟩
    · exact absurd (by simp [hdvd]) hu
  rw [hswap, tsum_congr hinner,
    ← (monomialFrobenius_injective (d := d) M hM).tsum_eq hsupport]
  have hterm : ∀ v : MonomialIndex d,
      overconvergentTateAlgebraCoefficient w (monomialFrobenius M v) g
          * (if ∀ i, M ∣ (monomialFrobenius M v) i then (M : K) ^ d else 0)
        = overconvergentTateAlgebraCoefficient w (monomialFrobenius M v) g * (M : K) ^ d := by
    intro v
    rw [if_pos fun i => (exists_monomialFrobenius_iff (monomialFrobenius M v)).mp ⟨v, rfl⟩ i]
  rw [tsum_congr hterm, tsum_mul_right, mul_comm]
end Evaluation
section NuclearRootsOfUnity
end NuclearRootsOfUnity
section SplittingEvaluation
section GenericEval
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
theorem tateEval_tateDilation {M : ℕ} (hM : M ≠ 0)
    (g : RamifiedOverconvergentTateAlgebra k p w)
    {x : Fin d → DworkCyclotomicField k p} (hx : ∀ i, ‖x i‖ = 1) :
    tateEval w (tateDilation k p w M g) x = tateEval w g (fun i => x i ^ M) := by
  have hxM : ∀ i, ‖(x i ^ M : DworkCyclotomicField k p)‖ = 1 := by
    intro i
    rw [norm_pow, hx i, one_pow]
  have hsupport : Function.support (tateEvalTerm w (tateDilation k p w M g) x)
      ⊆ Set.range (monomialFrobenius (d := d) M) := by
    intro u hu
    by_cases hdvd : ∃ v, monomialFrobenius M v = u
    · exact hdvd
    · exact absurd (by
        rw [tateEvalTerm, tateDilation_coefficient_of_not_dilated k p w M g u hdvd, zero_mul]) hu
  rw [tateEval, tateEval, ← (monomialFrobenius_injective (d := d) M hM).tsum_eq hsupport]
  refine tsum_congr fun v => ?_
  rw [tateEvalTerm, tateEvalTerm, tateDilation_coefficient_dilated k p w hM]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [monomialFrobenius_apply, pow_mul]
end GenericEval
theorem tateEval_ramifiedTateMonomial (v : MonomialIndex d) (b : DworkCyclotomicField k p)
    {x : Fin d → DworkCyclotomicField k p} (_hx : ∀ i, ‖x i‖ = 1) :
    tateEval w (ramifiedTateMonomial k p w v b) x = b * ∏ i, x i ^ v i := by
  classical
  rw [tateEval]
  have hterm : ∀ u : MonomialIndex d,
      tateEvalTerm w (ramifiedTateMonomial k p w v b) x u
        = if u = v then b * ∏ i, x i ^ v i else 0 := by
    intro u
    rw [tateEvalTerm, ramifiedTateMonomial, coefficient_finsuppToOverconvergentTateAlgebra]
    by_cases hu : u = v
    · subst hu
      simp
    · rw [Finsupp.single_apply, if_neg (fun h => hu h.symm), if_neg hu, zero_mul]
  rw [tsum_congr hterm, tsum_ite_eq]
theorem tateEval_dworkMonomialSplittingFactor (a : k) (u : MonomialIndex d)
    {x : Fin d → DworkCyclotomicField k p} (hx : ∀ i, ‖x i‖ = 1) :
    tateEval w (dworkMonomialSplittingFactor k p w a u) x
      = ∑' n : ℕ, PowerSeries.coeff n (dworkSplittingFunction k p)
          * (cyclotomicTeichmuller k p a * ∏ i, x i ^ u i) ^ n := by
  rw [dworkMonomialSplittingFactor,
    ← tateEvalCLM_apply w hx,
    (tateEvalCLM w hx).map_tsum (dworkMonomialSplittingTerm_hasSum k p w a u).summable]
  refine tsum_congr fun n => ?_
  have hprod : ∏ i, x i ^ (n • u) i = (∏ i, x i ^ u i) ^ n := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finsupp.smul_apply, smul_eq_mul, mul_comm, pow_mul]
  rw [tateEvalCLM_apply, dworkMonomialSplittingTerm, tateEval_smul w hx,
    ramifiedTateMonomial_pow, tateEval_ramifiedTateMonomial k p w _ _ hx, hprod, ← mul_pow]
  rfl
theorem tateEval_teichmullerSplittingProduct (f : MonomialIndex d →₀ k)
    {x : Fin d → DworkCyclotomicField k p} (hx : ∀ i, ‖x i‖ = 1) :
    tateEval w (teichmullerSplittingProduct k p w f) x
      = ∏ u ∈ f.support, ∑' n : ℕ, PowerSeries.coeff n (dworkSplittingFunction k p)
          * (cyclotomicTeichmuller k p (f u) * ∏ i, x i ^ u i) ^ n := by
  rw [teichmullerSplittingProduct, tateEval_prod w hx]
  exact Finset.prod_congr rfl fun u _ => tateEval_dworkMonomialSplittingFactor k p w (f u) u hx
theorem tateEval_ramifiedCoefficientwiseFrobeniusInv
    (g : RamifiedOverconvergentTateAlgebra k p w)
    {x : Fin d → DworkCyclotomicField k p} (hx : ∀ i, ‖x i‖ = 1) :
    tateEval w (ramifiedCoefficientwiseFrobeniusInv k p w g) x
      = (ramifiedCoefficientFrobenius k p).symm
          (tateEval w g (fun i => ramifiedCoefficientFrobenius k p (x i))) := by
  have hxσ : ∀ i, ‖ramifiedCoefficientFrobenius k p (x i)‖ = 1 := by
    intro i
    rw [ramifiedCoefficientFrobenius_norm, hx i]
  have hmap := ((summable_tateEvalTerm w g hxσ).hasSum).map
    ((ramifiedCoefficientFrobenius k p).symm.toAddMonoidHom)
    (ramifiedCoefficientFrobenius_symm_continuous k p)
  have heq : ∀ u : MonomialIndex d,
      ((ramifiedCoefficientFrobenius k p).symm.toAddMonoidHom ∘
        tateEvalTerm w g (fun i => ramifiedCoefficientFrobenius k p (x i))) u
        = tateEvalTerm w (ramifiedCoefficientwiseFrobeniusInv k p w g) x u := by
    intro u
    show (ramifiedCoefficientFrobenius k p).symm
        (tateEvalTerm w g (fun i => ramifiedCoefficientFrobenius k p (x i)) u) = _
    rw [tateEvalTerm, tateEvalTerm, ramifiedCoefficientwiseFrobeniusInv_coefficient,
      map_mul, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, RingEquiv.symm_apply_apply]
  have hgoal := hmap
  rw [funext heq] at hgoal
  rw [tateEval, hgoal.tsum_eq]
  rfl
private theorem ramifiedCoefficientFrobenius_iterate_pow (n : ℕ)
    (y : DworkCyclotomicField k p) (e : ℕ) :
    (ramifiedCoefficientFrobenius k p)^[n] (y ^ e)
      = ((ramifiedCoefficientFrobenius k p)^[n] y) ^ e := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, map_pow, ih, ← Function.iterate_succ_apply]
theorem tateEval_ramifiedCoefficientwiseFrobeniusInv_iterate (n : ℕ)
    (g : RamifiedOverconvergentTateAlgebra k p w)
    {x : Fin d → DworkCyclotomicField k p} (hx : ∀ i, ‖x i‖ = 1) :
    tateEval w ((ramifiedCoefficientwiseFrobeniusInv k p w)^[n] g) x
      = ((ramifiedCoefficientFrobenius k p).symm)^[n]
          (tateEval w g (fun i => (ramifiedCoefficientFrobenius k p)^[n] (x i))) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      have hxσ : ∀ i, ‖ramifiedCoefficientFrobenius k p (x i)‖ = 1 := by
        intro i
        rw [ramifiedCoefficientFrobenius_norm, hx i]
      rw [Function.iterate_succ_apply', tateEval_ramifiedCoefficientwiseFrobeniusInv k p w _ hx,
        ih hxσ, ← Function.iterate_succ_apply' (⇑(ramifiedCoefficientFrobenius k p).symm)]
      congr 2
theorem tateEval_dworkIteratedSplittingProduct (f : MonomialIndex d →₀ k) (m : ℕ)
    {x : Fin d → DworkCyclotomicField k p} (hx : ∀ i, ‖x i‖ = 1) :
    tateEval w (dworkIteratedSplittingProduct k p w f m) x
      = ∏ j ∈ Finset.range m,
          ((ramifiedCoefficientFrobenius k p).symm)^[m - j]
            (tateEval w (teichmullerSplittingProduct k p w f)
              (fun i => ((ramifiedCoefficientFrobenius k p)^[m - j] (x i)) ^ (p ^ j))) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
      have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
      have hxp : ∀ i, ‖(x i ^ p : DworkCyclotomicField k p)‖ = 1 := by
        intro i
        rw [norm_pow, hx i, one_pow]
      rw [dworkIteratedSplittingProduct_succ, tateEval_mul w hx,
        tateEval_tateDilation k p w hp _ hx, ih hxp,
        tateEval_ramifiedCoefficientwiseFrobeniusInv_iterate k p w (m + 1) _ hx,
        Finset.prod_range_succ']
      congr 1
      · refine Finset.prod_congr rfl fun j _ => ?_
        rw [Nat.succ_sub_succ]
        congr 2
        funext i
        rw [ramifiedCoefficientFrobenius_iterate_pow, ← pow_mul, ← pow_succ']
      · simp only [Nat.sub_zero, pow_zero, pow_one]
end SplittingEvaluation
section FrobeniusSplitting
theorem ramifiedCoefficientFrobenius_dworkArtinHasseEval (x : DworkCyclotomicField k p)
    (hx : ‖x‖ < 1) :
    ramifiedCoefficientFrobenius k p (dworkArtinHasseEval k p x)
      = dworkArtinHasseEval k p (ramifiedCoefficientFrobenius k p x) := by
  have hsum := hasSum_dworkPowerSeriesEval k p (dworkArtinHasseExponential k p) x
    (dworkArtinHasseExponential_coeff_norm_le_one k p) hx
  have hmap := hsum.map (ramifiedCoefficientFrobenius k p).toAddMonoidHom
    (ramifiedCoefficientFrobenius_continuous k p)
  have heq : ∀ n : ℕ,
      ((ramifiedCoefficientFrobenius k p).toAddMonoidHom ∘
        fun n : ℕ => PowerSeries.coeff n (dworkArtinHasseExponential k p) * x ^ n) n
      = PowerSeries.coeff n (dworkArtinHasseExponential k p)
          * (ramifiedCoefficientFrobenius k p x) ^ n := by
    intro n
    show ramifiedCoefficientFrobenius k p
        (PowerSeries.coeff n (dworkArtinHasseExponential k p) * x ^ n) = _
    rw [map_mul, map_pow, dworkArtinHasseExponential, PowerSeries.coeff_map]
    congr 1
    exact map_ratCast _ _
  rw [funext heq] at hmap
  rw [dworkArtinHasseEval_eq_tsum k p]
  exact hmap.tsum_eq.symm
@[simp]
theorem ramifiedCoefficientFrobenius_dworkArtinHasseParameter :
    ramifiedCoefficientFrobenius k p (dworkArtinHasseParameter k p)
      = dworkArtinHasseParameter k p := by
  refine dworkArtinHasseParameter_unique k p ?_ ?_ ?_
  · rw [ramifiedCoefficientFrobenius_norm]
    exact (existsUnique_dworkArtinHasseParameter k p).choose_spec.1.1
  · rw [ramifiedCoefficientFrobenius_norm]
    exact dworkArtinHasseParameter_norm_lt_one k p
  · rw [← ramifiedCoefficientFrobenius_dworkArtinHasseEval k p _
      (dworkArtinHasseParameter_norm_lt_one k p), dworkArtinHasseParameter_spec,
      ramifiedCoefficientFrobenius_dworkPrimitiveRoot]
@[simp]
theorem ramifiedCoefficientFrobenius_dworkSplittingFunction_coeff (n : ℕ) :
    ramifiedCoefficientFrobenius k p (PowerSeries.coeff n (dworkSplittingFunction k p))
      = PowerSeries.coeff n (dworkSplittingFunction k p) := by
  conv_rhs => rw [dworkSplittingFunction_coeff]
  rw [dworkSplittingFunction_coeff, map_mul, map_pow,
    ramifiedCoefficientFrobenius_dworkArtinHasseParameter]
  congr 1
  rw [dworkArtinHasseExponential, PowerSeries.coeff_map]
  exact map_ratCast _ _
@[simp]
theorem ramifiedCoefficientFrobenius_symm_dworkSplittingFunction_coeff (n : ℕ) :
    (ramifiedCoefficientFrobenius k p).symm (PowerSeries.coeff n (dworkSplittingFunction k p))
      = PowerSeries.coeff n (dworkSplittingFunction k p) := by
  rw [RingEquiv.symm_apply_eq, ramifiedCoefficientFrobenius_dworkSplittingFunction_coeff]
@[simp]
theorem residueFrobeniusInv_pow (a : k) : (residueFrobeniusInv k p a) ^ p = a := by
  have := (frobeniusEquiv k p).apply_symm_apply a
  rwa [frobeniusEquiv_apply, frobenius_def] at this
theorem ramifiedCoefficientFrobenius_symm_ramifiedTeichmullerLift (a : k) :
    (ramifiedCoefficientFrobenius k p).symm (ramifiedTeichmullerLift k p a)
      = ramifiedTeichmullerLift k p (residueFrobeniusInv k p a) := by
  rw [RingEquiv.symm_apply_eq, ramifiedCoefficientFrobenius_ramifiedTeichmullerLift,
    residueFrobeniusInv_pow]
theorem ramifiedCoefficientwiseFrobeniusInv_ramifiedTateMonomial (v : MonomialIndex d)
    (b : DworkCyclotomicField k p) :
    ramifiedCoefficientwiseFrobeniusInv k p w (ramifiedTateMonomial k p w v b)
      = ramifiedTateMonomial k p w v ((ramifiedCoefficientFrobenius k p).symm b) := by
  refine tate_ext k p w fun u => ?_
  rw [ramifiedCoefficientwiseFrobeniusInv_coefficient, ramifiedTateMonomial,
    ramifiedTateMonomial, coefficient_finsuppToOverconvergentTateAlgebra,
    coefficient_finsuppToOverconvergentTateAlgebra, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> simp
theorem ramifiedCoefficientwiseFrobeniusInv_dworkMonomialSplittingFactor
    (a : k) (u : MonomialIndex d) :
    ramifiedCoefficientwiseFrobeniusInv k p w (dworkMonomialSplittingFactor k p w a u)
      = dworkMonomialSplittingFactor k p w (residueFrobeniusInv k p a) u := by
  have hmap := (dworkMonomialSplittingTerm_hasSum k p w a u).map
    (ramifiedCoefficientwiseFrobeniusInv k p w)
    (ramifiedCoefficientwiseFrobeniusInv_continuous k p w)
  have heq : ∀ n : ℕ,
      ((ramifiedCoefficientwiseFrobeniusInv k p w) ∘ dworkMonomialSplittingTerm k p w a u) n
        = dworkMonomialSplittingTerm k p w (residueFrobeniusInv k p a) u n := by
    intro n
    show ramifiedCoefficientwiseFrobeniusInv k p w
      (dworkMonomialSplittingTerm k p w a u n) = _
    rw [dworkMonomialSplittingTerm, dworkMonomialSplittingTerm,
      ramifiedCoefficientwiseFrobeniusInv_smul,
      ramifiedCoefficientFrobenius_symm_dworkSplittingFunction_coeff,
      ramifiedTateMonomial_pow, ramifiedTateMonomial_pow,
      ramifiedCoefficientwiseFrobeniusInv_ramifiedTateMonomial, map_pow]
    congr 2
    exact congrArg (fun z => z ^ n)
      (ramifiedCoefficientFrobenius_symm_ramifiedTeichmullerLift k p a)
  rw [funext heq] at hmap
  rw [dworkMonomialSplittingFactor]
  exact hmap.tsum_eq.symm
theorem ramifiedCoefficientwiseFrobeniusInv_teichmullerSplittingProduct
    (f : MonomialIndex d →₀ k) :
    ramifiedCoefficientwiseFrobeniusInv k p w (teichmullerSplittingProduct k p w f)
      = teichmullerSplittingProduct k p w
          (Finsupp.mapRange (residueFrobeniusInv k p) (map_zero _) f) := by
  classical
  have hsupp : (Finsupp.mapRange (residueFrobeniusInv k p) (map_zero _) f).support = f.support :=
    Finsupp.support_mapRange_of_injective (map_zero _) f (residueFrobeniusInv k p).injective
  rw [teichmullerSplittingProduct, teichmullerSplittingProduct, hsupp]
  induction f.support using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        ramifiedCoefficientwiseFrobeniusInv_mul, ih,
        ramifiedCoefficientwiseFrobeniusInv_dworkMonomialSplittingFactor]
      rfl
@[simp]
theorem residueFrobeniusTwist_zero (f : MonomialIndex d →₀ k) :
    residueFrobeniusTwist k p 0 f = f := by
  ext u
  rfl
theorem residueFrobeniusTwist_succ (m : ℕ) (f : MonomialIndex d →₀ k) :
    residueFrobeniusTwist k p (m + 1) f
      = Finsupp.mapRange (residueFrobeniusInv k p) (map_zero _)
          (residueFrobeniusTwist k p m f) := by
  ext u
  simp only [residueFrobeniusTwist_apply, Finsupp.mapRange_apply]
  rw [Function.iterate_succ_apply']
theorem ramifiedCoefficientwiseFrobeniusInv_iterate_teichmullerSplittingProduct (m : ℕ)
    (f : MonomialIndex d →₀ k) :
    (ramifiedCoefficientwiseFrobeniusInv k p w)^[m] (teichmullerSplittingProduct k p w f)
      = teichmullerSplittingProduct k p w (residueFrobeniusTwist k p m f) := by
  induction m with
  | zero => rw [Function.iterate_zero_apply, residueFrobeniusTwist_zero]
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih,
        ramifiedCoefficientwiseFrobeniusInv_teichmullerSplittingProduct,
        residueFrobeniusTwist_succ]
end FrobeniusSplitting
section PhiFree
theorem tateDilation_one_eq (g : RamifiedOverconvergentTateAlgebra k p w) :
    tateDilation k p w 1 g = g := by
  refine tate_ext k p w fun u => ?_
  have h := tateDilation_coefficient_dilated k p w (m := 1) one_ne_zero g u
  rwa [show monomialFrobenius 1 u = u from by simp [monomialFrobenius]] at h
theorem tateDilation_tateDilation {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (g : RamifiedOverconvergentTateAlgebra k p w) :
    tateDilation k p w m (tateDilation k p w n g) = tateDilation k p w (m * n) g := by
  classical
  refine tate_ext k p w fun u => ?_
  by_cases hu : ∃ v, monomialFrobenius (m * n) v = u
  · obtain ⟨v, rfl⟩ := hu
    have hsplit : monomialFrobenius (m * n) v = monomialFrobenius m (monomialFrobenius n v) := by
      ext i
      simp only [monomialFrobenius_apply]
      ring
    rw [tateDilation_coefficient_dilated k p w (Nat.mul_ne_zero hm hn) g v, hsplit,
      tateDilation_coefficient_dilated k p w hm, tateDilation_coefficient_dilated k p w hn]
  · rw [tateDilation_coefficient_of_not_dilated k p w (m * n) g u hu]
    by_cases hu' : ∃ v, monomialFrobenius m v = u
    · obtain ⟨v, rfl⟩ := hu'
      rw [tateDilation_coefficient_dilated k p w hm]
      refine tateDilation_coefficient_of_not_dilated k p w n g v ?_
      rintro ⟨v', rfl⟩
      exact hu ⟨v', by ext i; simp only [monomialFrobenius_apply]; ring⟩
    · rw [tateDilation_coefficient_of_not_dilated k p w m _ u hu']
theorem dworkIteratedSplittingProduct_eq_prod (f : MonomialIndex d →₀ k) (m : ℕ) :
    dworkIteratedSplittingProduct k p w f m
      = ∏ j ∈ Finset.range m,
          tateDilation k p w (p ^ j)
            (teichmullerSplittingProduct k p w (residueFrobeniusTwist k p (m - j) f)) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  induction m with
  | zero => simp
  | succ m ih =>
      rw [dworkIteratedSplittingProduct_succ, ih,
        ramifiedCoefficientwiseFrobeniusInv_iterate_teichmullerSplittingProduct,
        ← tateDilationRingHom_apply k p w hp, map_prod, Finset.prod_range_succ']
      refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun j hj => ?_) ?_
      · have hidx : m + 1 - (j + 1) = m - j := by omega
        rw [tateDilationRingHom_apply,
          tateDilation_tateDilation k p w hp (pow_ne_zero _ hp), ← pow_succ', hidx]
      · rw [pow_zero, tateDilation_one_eq, Nat.sub_zero]
end PhiFree
end FiniteFields.Dwork
end
end
section
noncomputable section
open Filter Topology
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
attribute [local instance] dw5cResiduePrimeAlgebra
variable {d : ℕ} (w : PositiveMonomialWeight d)
section TateBaseChange
variable (K : Type*) [Field K] [CharP K p] [Finite K] [Algebra k K]
@[simp]
theorem tateBaseChange_one :
    tateBaseChange k p w K (1 : RamifiedOverconvergentTateAlgebra k p w) = 1 := by
  refine tate_ext K p w fun u => ?_
  rw [tateBaseChange_coefficient, coefficient_one', coefficient_one']
  split_ifs <;> simp
theorem tateBaseChange_mul (g h : RamifiedOverconvergentTateAlgebra k p w) :
    tateBaseChange k p w K (g * h) = tateBaseChange k p w K g * tateBaseChange k p w K h := by
  refine tate_ext K p w fun u => ?_
  rw [tateBaseChange_coefficient, coefficient_mul', coefficient_mul', map_sum]
  refine Finset.sum_congr rfl fun xy _ => ?_
  rw [map_mul, tateBaseChange_coefficient, tateBaseChange_coefficient]
theorem tateBaseChange_smul (c : DworkCyclotomicField k p)
    (g : RamifiedOverconvergentTateAlgebra k p w) :
    tateBaseChange k p w K (c • g)
      = dworkCyclotomicBaseChange k p K c • tateBaseChange k p w K g := by
  refine tate_ext K p w fun u => ?_
  have h1 : overconvergentTateAlgebraCoefficient w u (c • g)
      = c * overconvergentTateAlgebraCoefficient w u g := by
    rw [map_smul, smul_eq_mul]
  have h2 : overconvergentTateAlgebraCoefficient w u
      (dworkCyclotomicBaseChange k p K c • tateBaseChange k p w K g)
      = dworkCyclotomicBaseChange k p K c
        * overconvergentTateAlgebraCoefficient w u (tateBaseChange k p w K g) := by
    rw [map_smul, smul_eq_mul]
  rw [tateBaseChange_coefficient, h1, h2, tateBaseChange_coefficient, map_mul]
theorem norm_tateBaseChange_le (g : RamifiedOverconvergentTateAlgebra k p w) :
    ‖tateBaseChange k p w K g‖ ≤ ‖g‖ := by
  rw [← OverconvergentTateAlgebra.norm_toSeries,
    ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le (norm_nonneg g)).2 fun U => ?_
  show ‖dworkCyclotomicBaseChange k p K (g.toSeries U)‖ ≤ ‖g‖
  rw [norm_dworkCyclotomicBaseChange]
  rw [← OverconvergentTateAlgebra.norm_toSeries, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact BoundedContinuousFunction.norm_coe_le_norm g.toSeries.toBCF U
theorem tateBaseChange_continuous : Continuous (tateBaseChange k p w K) :=
  AddMonoidHomClass.continuous_of_bound (tateBaseChangeAddHom k p w K) 1 fun g => by
    show ‖tateBaseChange k p w K g‖ ≤ 1 * ‖g‖
    simpa only [one_mul] using norm_tateBaseChange_le k p w K g
theorem tateBaseChange_ramifiedTateMonomial (v : MonomialIndex d)
    (b : DworkCyclotomicField k p) :
    tateBaseChange k p w K (ramifiedTateMonomial k p w v b)
      = ramifiedTateMonomial K p w v (dworkCyclotomicBaseChange k p K b) := by
  refine tate_ext K p w fun u => ?_
  rw [tateBaseChange_coefficient, ramifiedTateMonomial, ramifiedTateMonomial,
    coefficient_finsuppToOverconvergentTateAlgebra, coefficient_finsuppToOverconvergentTateAlgebra,
    Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> simp
theorem tateBaseChange_dworkMonomialSplittingFactor (a : k) (u : MonomialIndex d) :
    tateBaseChange k p w K (dworkMonomialSplittingFactor k p w a u)
      = dworkMonomialSplittingFactor K p w (algebraMap k K a) u := by
  have hmap := (dworkMonomialSplittingTerm_hasSum k p w a u).map
    (tateBaseChangeAddHom k p w K) (tateBaseChange_continuous k p w K)
  have heq : ∀ n : ℕ,
      ((tateBaseChangeAddHom k p w K) ∘ dworkMonomialSplittingTerm k p w a u) n
        = dworkMonomialSplittingTerm K p w (algebraMap k K a) u n := by
    intro n
    show tateBaseChange k p w K (dworkMonomialSplittingTerm k p w a u n) = _
    rw [dworkMonomialSplittingTerm, dworkMonomialSplittingTerm, tateBaseChange_smul,
      dworkCyclotomicBaseChange_dworkSplittingFunction_coeff, ramifiedTateMonomial_pow,
      ramifiedTateMonomial_pow, tateBaseChange_ramifiedTateMonomial, map_pow]
    congr 2
    exact congrArg (fun z => z ^ n)
      (dworkCyclotomicBaseChange_ramifiedTeichmullerLift k p K a)
  rw [funext heq] at hmap
  rw [dworkMonomialSplittingFactor]
  exact hmap.tsum_eq.symm
omit [Finite k] [Finite K] in
theorem residueBaseChange_support (f : MonomialIndex d →₀ k) :
    (residueBaseChange (k := k) (K := K) f).support = f.support :=
  Finsupp.support_mapRange_of_injective (map_zero _) f (algebraMap k K).injective
theorem tateBaseChange_teichmullerSplittingProduct (f : MonomialIndex d →₀ k) :
    tateBaseChange k p w K (teichmullerSplittingProduct k p w f)
      = teichmullerSplittingProduct K p w (residueBaseChange (k := k) (K := K) f) := by
  classical
  rw [teichmullerSplittingProduct, teichmullerSplittingProduct, residueBaseChange_support]
  induction f.support using Finset.induction_on with
  | empty => simp [tateBaseChange_one k p w K]
  | insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, tateBaseChange_mul, ih,
        tateBaseChange_dworkMonomialSplittingFactor]
      rfl
theorem tateBaseChange_tateDilation {m : ℕ} (hm : m ≠ 0)
    (g : RamifiedOverconvergentTateAlgebra k p w) :
    tateBaseChange k p w K (tateDilation k p w m g)
      = tateDilation K p w m (tateBaseChange k p w K g) := by
  classical
  refine tate_ext K p w fun u => ?_
  by_cases hu : ∃ v, monomialFrobenius m v = u
  · obtain ⟨v, rfl⟩ := hu
    rw [tateBaseChange_coefficient, tateDilation_coefficient_dilated k p w hm,
      tateDilation_coefficient_dilated K p w hm, tateBaseChange_coefficient]
  · rw [tateBaseChange_coefficient, tateDilation_coefficient_of_not_dilated k p w m g u hu,
      tateDilation_coefficient_of_not_dilated K p w m _ u hu, map_zero]
theorem algebraMap_residueFrobeniusInv (a : k) :
    algebraMap k K (residueFrobeniusInv k p a) = residueFrobeniusInv K p (algebraMap k K a) := by
  have h1 : (algebraMap k K (residueFrobeniusInv k p a)) ^ p = algebraMap k K a := by
    rw [← map_pow, residueFrobeniusInv_pow]
  have h2 : (residueFrobeniusInv K p (algebraMap k K a)) ^ p = algebraMap k K a :=
    residueFrobeniusInv_pow K p _
  refine (frobeniusEquiv K p).injective ?_
  simpa only [frobeniusEquiv_apply, frobenius_def] using h1.trans h2.symm
theorem residueBaseChange_residueFrobeniusTwist (m : ℕ) (f : MonomialIndex d →₀ k) :
    residueBaseChange (k := k) (K := K) (residueFrobeniusTwist k p m f)
      = residueFrobeniusTwist K p m (residueBaseChange (k := k) (K := K) f) := by
  ext u
  simp only [residueBaseChange_apply, residueFrobeniusTwist_apply]
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        algebraMap_residueFrobeniusInv, ih]
theorem tateBaseChange_dworkIteratedSplittingProduct (f : MonomialIndex d →₀ k) (m : ℕ) :
    tateBaseChange k p w K (dworkIteratedSplittingProduct k p w f m)
      = dworkIteratedSplittingProduct K p w (residueBaseChange (k := k) (K := K) f) m := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [dworkIteratedSplittingProduct_eq_prod, dworkIteratedSplittingProduct_eq_prod]
  induction Finset.range m using Finset.induction_on with
  | empty => simp [tateBaseChange_one k p w K]
  | insert j t hj ih =>
      rw [Finset.prod_insert hj, Finset.prod_insert hj, tateBaseChange_mul, ih,
        tateBaseChange_tateDilation k p w K (pow_ne_zero _ hp),
        tateBaseChange_teichmullerSplittingProduct,
        residueBaseChange_residueFrobeniusTwist]
end TateBaseChange
end FiniteFields.Dwork
end
end
section
noncomputable section
open Filter Topology
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
attribute [local instance] dw5cResiduePrimeAlgebra
variable {d : ℕ} (w : PositiveMonomialWeight d)
section TraceTransport
variable (K : Type*) [Field K] [CharP K p] [Finite K] [Algebra k K]
theorem dworkCyclotomicBaseChange_tracePower (f : MonomialIndex d →₀ k) (s : ℕ+)
    (hK : Module.finrank (ZMod p) K = Module.finrank (ZMod p) k * (s : ℕ)) :
    dworkCyclotomicBaseChange k p K
        (NuclearOperator.tracePower w (dworkQFrobeniusNuclearOperator k p w f) s)
      = NuclearOperator.tracePower w
          (dworkQFrobeniusNuclearOperator K p w (residueBaseChange (k := k) (K := K) f)) 1 := by
  have hQ : dworkQPow K p 1 = dworkQPow k p (s : ℕ) := by
    rw [dworkQPow, dworkQPow, mul_one, hK]
  have hm : Module.finrank (ZMod p) K * 1 = Module.finrank (ZMod p) k * (s : ℕ) := by
    rw [mul_one, hK]
  have hpoint : ∀ u : MonomialIndex d,
      dworkCyclotomicBaseChange k p K (dworkSplittingDiagonal k p w f (s : ℕ) u)
        = dworkSplittingDiagonal K p w (residueBaseChange (k := k) (K := K) f) 1 u := by
    intro u
    rw [dworkSplittingDiagonal, dworkSplittingDiagonal, hQ, hm,
      ← tateBaseChange_coefficient k p w K, tateBaseChange_dworkIteratedSplittingProduct]
  have hsum := (summable_dworkSplittingDiagonal k p w f s.2).hasSum
  have hmap' : HasSum
      (fun u : MonomialIndex d =>
        dworkCyclotomicBaseChange k p K (dworkSplittingDiagonal k p w f (s : ℕ) u))
      (dworkCyclotomicBaseChange k p K
        (∑' u : MonomialIndex d, dworkSplittingDiagonal k p w f (s : ℕ) u)) :=
    hsum.map (dworkCyclotomicBaseChange k p K).toAddMonoidHom
      (dworkCyclotomicBaseChange_continuous k p K)
  rw [funext hpoint] at hmap'
  rw [dworkTracePower_eq_splittingSum, dworkTracePower_eq_splittingSum]
  exact hmap'.tsum_eq.symm
end TraceTransport
end FiniteFields.Dwork
end
end
section
noncomputable section
open Filter Topology
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
attribute [local instance] dw5cResiduePrimeAlgebra
variable {d : ℕ} (w : PositiveMonomialWeight d)
section TeichmullerPoints
theorem ramifiedTeichmullerLift_pow (a : k) (n : ℕ) :
    ramifiedTeichmullerLift k p (a ^ n) = ramifiedTeichmullerLift k p a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ramifiedTeichmullerLift_mul, ih, pow_succ]
theorem ramifiedTeichmullerLift_prod {ι : Type*} (t : Finset ι) (g : ι → k) :
    ramifiedTeichmullerLift k p (∏ i ∈ t, g i)
      = ∏ i ∈ t, ramifiedTeichmullerLift k p (g i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, ramifiedTeichmullerLift_mul, ih]
theorem ramifiedCoefficientFrobenius_dworkSplittingValue (z : k) :
    ramifiedCoefficientFrobenius k p (dworkSplittingValue k p z)
      = dworkSplittingValue k p (z ^ p) := by
  have hsum := hasSum_dworkSplittingValue k p z
  have hmap : HasSum
      (fun n : ℕ => ramifiedCoefficientFrobenius k p
        (PowerSeries.coeff n (dworkSplittingFunction k p)
          * ramifiedTeichmullerLift k p z ^ n))
      (ramifiedCoefficientFrobenius k p (dworkSplittingValue k p z)) :=
    hsum.map (ramifiedCoefficientFrobenius k p).toAddMonoidHom
      (ramifiedCoefficientFrobenius_continuous k p)
  have hpoint : ∀ n : ℕ, ramifiedCoefficientFrobenius k p
      (PowerSeries.coeff n (dworkSplittingFunction k p)
        * ramifiedTeichmullerLift k p z ^ n)
      = PowerSeries.coeff n (dworkSplittingFunction k p)
          * ramifiedTeichmullerLift k p (z ^ p) ^ n := by
    intro n
    rw [map_mul, map_pow, ramifiedCoefficientFrobenius_dworkSplittingFunction_coeff,
      ramifiedCoefficientFrobenius_ramifiedTeichmullerLift]
  rw [funext hpoint] at hmap
  exact ((hasSum_dworkSplittingValue k p (z ^ p)).unique hmap).symm
theorem ramifiedCoefficientFrobenius_symm_dworkSplittingValue (z : k) :
    (ramifiedCoefficientFrobenius k p).symm (dworkSplittingValue k p z)
      = dworkSplittingValue k p (residueFrobeniusInv k p z) := by
  rw [RingEquiv.symm_apply_eq, ramifiedCoefficientFrobenius_dworkSplittingValue,
    residueFrobeniusInv_pow]
theorem ramifiedCoefficientFrobenius_symm_iterate_dworkSplittingValue (m : ℕ) (z : k) :
    ((ramifiedCoefficientFrobenius k p).symm)^[m] (dworkSplittingValue k p z)
      = dworkSplittingValue k p ((residueFrobeniusInv k p)^[m] z) := by
  induction m generalizing z with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply, ramifiedCoefficientFrobenius_symm_dworkSplittingValue, ih,
        Function.iterate_succ_apply]
theorem ramifiedCoefficientFrobenius_iterate_ramifiedTeichmullerLift (m : ℕ) (a : k) :
    (ramifiedCoefficientFrobenius k p)^[m] (ramifiedTeichmullerLift k p a)
      = ramifiedTeichmullerLift k p (a ^ (p ^ m)) := by
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, ramifiedCoefficientFrobenius_ramifiedTeichmullerLift, ih,
        ← pow_mul, ← pow_succ']
private theorem pow_pow_injective (m : ℕ) : Function.Injective (fun y : k => y ^ (p ^ m)) := by
  induction m with
  | zero =>
      intro x y h
      simpa using h
  | succ m ih =>
      have hcomp : (fun y : k => y ^ (p ^ (m + 1)))
          = (fun z : k => z ^ p) ∘ (fun y : k => y ^ (p ^ m)) := by
        funext y
        simp [pow_succ, pow_mul]
      rw [hcomp]
      refine Function.Injective.comp (fun x y hxy => ?_) ih
      exact (frobeniusEquiv k p).injective (by simpa [frobeniusEquiv_apply, frobenius_def] using hxy)
theorem residueFrobeniusInv_iterate_pow (m : ℕ) (z : k) :
    ((residueFrobeniusInv k p)^[m] z) ^ (p ^ m) = z := by
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih, residueFrobeniusInv_pow]
theorem residueFrobeniusInv_iterate_eq_pow {m : ℕ}
    (hm : m ≤ Module.finrank (ZMod p) k) (z : k) :
    (residueFrobeniusInv k p)^[m] z = z ^ (p ^ (Module.finrank (ZMod p) k - m)) := by
  refine pow_pow_injective k p m ?_
  show ((residueFrobeniusInv k p)^[m] z) ^ (p ^ m) = (z ^ (p ^ (Module.finrank (ZMod p) k - m))) ^ (p ^ m)
  rw [residueFrobeniusInv_iterate_pow, ← pow_mul, ← pow_add,
    show Module.finrank (ZMod p) k - m + m = Module.finrank (ZMod p) k from by omega]
  letI := Fintype.ofFinite k
  rw [FiniteField.pow_finrank_eq_natCard p k, Nat.card_eq_fintype_card, FiniteField.pow_card]
end TeichmullerPoints
section CharacterIdentification
theorem cyclotomicTeichmuller_eq (a : k) :
    cyclotomicTeichmuller k p a = ramifiedTeichmullerLift k p a := rfl
private theorem ramifiedCoefficientFrobenius_symm_iterate_prod {ι : Type*} (m : ℕ) (t : Finset ι)
    (g : ι → DworkCyclotomicField k p) :
    ((ramifiedCoefficientFrobenius k p).symm)^[m] (∏ i ∈ t, g i)
      = ∏ i ∈ t, ((ramifiedCoefficientFrobenius k p).symm)^[m] (g i) := by
  induction m generalizing g with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, map_prod, ih]
      exact Finset.prod_congr rfl fun i _ => (Function.iterate_succ_apply _ m (g i)).symm
theorem tateEval_teichmullerSplittingProduct_teichmuller (f : MonomialIndex d →₀ k)
    (y : Fin d → k) (hy : ∀ i, y i ≠ 0) :
    tateEval w (teichmullerSplittingProduct k p w f)
        (fun i => ramifiedTeichmullerLift k p (y i))
      = ∏ u ∈ f.support, dworkSplittingValue k p (f u * ∏ i, y i ^ u i) := by
  have hx : ∀ i, ‖ramifiedTeichmullerLift k p (y i)‖ = 1 := fun i =>
    ramifiedTeichmullerLift_norm_of_ne_zero k p (hy i)
  rw [tateEval_teichmullerSplittingProduct k p w f hx]
  refine Finset.prod_congr rfl fun u _ => ?_
  have hbase : cyclotomicTeichmuller k p (f u)
      * ∏ i, ramifiedTeichmullerLift k p (y i) ^ u i
      = ramifiedTeichmullerLift k p (f u * ∏ i, y i ^ u i) := by
    rw [cyclotomicTeichmuller_eq, ramifiedTeichmullerLift_mul, ramifiedTeichmullerLift_prod]
    exact congrArg _ (Finset.prod_congr rfl fun i _ =>
      (ramifiedTeichmullerLift_pow k p (y i) (u i)).symm)
  rw [hbase, dworkSplittingValue_eq_tsum]
theorem tateEval_dworkIteratedSplittingProduct_teichmuller (f : MonomialIndex d →₀ k)
    (y : Fin d → k) (hy : ∀ i, y i ≠ 0) :
    tateEval w (dworkIteratedSplittingProduct k p w f (Module.finrank (ZMod p) k))
        (fun i => ramifiedTeichmullerLift k p (y i))
      = dworkTraceAdditiveCharacter k p (finitePolynomialEval k k f y) := by
  classical
  letI := Fintype.ofFinite k
  have hx : ∀ i, ‖ramifiedTeichmullerLift k p (y i)‖ = 1 := fun i =>
    ramifiedTeichmullerLift_norm_of_ne_zero k p (hy i)
  rw [tateEval_dworkIteratedSplittingProduct k p w f (Module.finrank (ZMod p) k) hx]
  have hstep : ∀ j ∈ Finset.range (Module.finrank (ZMod p) k),
      ((ramifiedCoefficientFrobenius k p).symm)^[Module.finrank (ZMod p) k - j]
        (tateEval w (teichmullerSplittingProduct k p w f)
          (fun i => ((ramifiedCoefficientFrobenius k p)^[Module.finrank (ZMod p) k - j]
            (ramifiedTeichmullerLift k p (y i))) ^ (p ^ j)))
        = ∏ u ∈ f.support,
            dworkSplittingValue k p ((f u * ∏ i, y i ^ u i) ^ (p ^ j)) := by
    intro j hj
    have hjlt : j < Module.finrank (ZMod p) k := Finset.mem_range.mp hj
    have harg : ∀ i, ((ramifiedCoefficientFrobenius k p)^[Module.finrank (ZMod p) k - j]
        (ramifiedTeichmullerLift k p (y i))) ^ (p ^ j)
        = ramifiedTeichmullerLift k p (y i) := by
      intro i
      rw [ramifiedCoefficientFrobenius_iterate_ramifiedTeichmullerLift,
        ← ramifiedTeichmullerLift_pow, ← pow_mul, ← pow_add,
        show Module.finrank (ZMod p) k - j + j = Module.finrank (ZMod p) k from by omega,
        FiniteField.pow_finrank_eq_natCard p k, Nat.card_eq_fintype_card, FiniteField.pow_card]
    rw [funext harg, tateEval_teichmullerSplittingProduct_teichmuller k p w f y hy,
      ramifiedCoefficientFrobenius_symm_iterate_prod]
    refine Finset.prod_congr rfl fun u _ => ?_
    rw [ramifiedCoefficientFrobenius_symm_iterate_dworkSplittingValue,
      residueFrobeniusInv_iterate_eq_pow k p (by omega),
      show Module.finrank (ZMod p) k - (Module.finrank (ZMod p) k - j) = j from by omega]
  rw [Finset.prod_congr rfl hstep, Finset.prod_comm]
  have hchar : ∀ u ∈ f.support,
      (∏ j ∈ Finset.range (Module.finrank (ZMod p) k),
        dworkSplittingValue k p ((f u * ∏ i, y i ^ u i) ^ (p ^ j)))
      = dworkTraceAdditiveCharacter k p (f u * ∏ i, y i ^ u i) := by
    intro u _
    exact dworkFrobeniusConjugateProduct_eq_character k p _
  rw [Finset.prod_congr rfl hchar, ← addChar_map_sum, finitePolynomialEval_eq_sum]
  simp
end CharacterIdentification
section TeichmullerTorus
theorem ramifiedTeichmullerLift_injective :
    Function.Injective (ramifiedTeichmullerLift k p) := by
  intro a b hab
  have h1 : coefficientRingAlgebraMap k p (teichmullerLift k p a)
      = coefficientRingAlgebraMap k p (teichmullerLift k p b) :=
    (algebraMap (CoefficientField k p) (DworkCyclotomicField k p)).injective hab
  have h2 : teichmullerLift k p a = teichmullerLift k p b :=
    coefficientRingAlgebraMap_injective k p h1
  have h3 := congrArg (residueMap k p) h2
  rwa [residueMap_teichmullerLift, residueMap_teichmullerLift] at h3
theorem isPrimitiveRoot_ramifiedTeichmullerLift {g : kˣ}
    (hg : ∀ y : kˣ, y ∈ Subgroup.zpowers g) :
    IsPrimitiveRoot (ramifiedTeichmullerLift k p (g : k)) (Nat.card k - 1) := by
  have hord : orderOf g = Nat.card k - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]
  refine ⟨?_, ?_⟩
  · rw [← ramifiedTeichmullerLift_pow]
    have : (g : k) ^ (Nat.card k - 1) = 1 := by
      rw [← hord, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
    rw [this, ramifiedTeichmullerLift_one]
  · intro l hl
    rw [← ramifiedTeichmullerLift_pow] at hl
    have hl' : (g : k) ^ l = 1 := by
      have := hl.trans (ramifiedTeichmullerLift_one k p).symm
      exact ramifiedTeichmullerLift_injective k p this
    have hlu : g ^ l = 1 := Units.ext (by rwa [Units.val_pow_eq_pow_val, Units.val_one])
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hlu
theorem sum_teichmullerTorus_tateEval [Fintype k] [DecidableEq k]
    (g : RamifiedOverconvergentTateAlgebra k p w) :
    ∑ y : Fin d → kˣ, tateEval w g (fun i => ramifiedTeichmullerLift k p ((y i : k)))
      = ((Nat.card k - 1 : ℕ) : DworkCyclotomicField k p) ^ d
        * ∑' u : MonomialIndex d,
            overconvergentTateAlgebraCoefficient w
              (monomialFrobenius (Nat.card k - 1) u) g := by
  set M : ℕ := Nat.card k - 1 with hM
  have hMcard : Fintype.card kˣ = M := by
    rw [hM, ← Nat.card_units (α := k), Nat.card_eq_fintype_card]
  have hM0 : M ≠ 0 := by
    have h1 : 1 < Nat.card k := Finite.one_lt_card
    omega
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_monoid_generator (α := kˣ)
  have hzp : ∀ y : kˣ, y ∈ Subgroup.zpowers g₀ := fun y =>
    Subgroup.mem_zpowers_iff.mpr (by
      obtain ⟨i, hi⟩ := hg₀ y
      exact ⟨(i : ℤ), by rw [zpow_natCast]; exact hi⟩)
  have hord : orderOf g₀ = M := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hzp, hM, Nat.card_units]
  have hζ : IsPrimitiveRoot (ramifiedTeichmullerLift k p ((g₀ : k))) M :=
    isPrimitiveRoot_ramifiedTeichmullerLift k p hzp
  have hinj : Function.Injective (fun t : Fin M => g₀ ^ (t : ℕ)) := by
    intro s t hst
    have hs : (s : ℕ) < orderOf g₀ := by rw [hord]; exact s.2
    have ht : (t : ℕ) < orderOf g₀ := by rw [hord]; exact t.2
    exact Fin.ext (pow_injOn_Iio_orderOf hs ht hst)
  have hbij : Function.Bijective (fun t : Fin M => g₀ ^ (t : ℕ)) := by
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
    rw [Fintype.card_fin, hMcard]
  set e : Fin M ≃ kˣ := Equiv.ofBijective _ hbij with he
  rw [← sum_rootsOfUnity_tateEval w hM0 hζ]
  refine (Fintype.sum_equiv (Equiv.piCongrRight fun _ : Fin d => e) _ _ fun t => ?_).symm
  refine congrArg (tateEval w g) (funext fun i => ?_)
  show ramifiedTeichmullerLift k p ((g₀ : k)) ^ ((t i : ℕ))
      = ramifiedTeichmullerLift k p ((e (t i) : kˣ) : k)
  rw [← ramifiedTeichmullerLift_pow]
  congr 1
end TeichmullerTorus
section FirstPowerCharacterSum
theorem dworkTracePower_one_eq_characterSum [Fintype k] [DecidableEq k]
    (f : MonomialIndex d →₀ k) :
    ((Nat.card k - 1 : ℕ) : DworkCyclotomicField k p) ^ d
        * NuclearOperator.tracePower w (dworkQFrobeniusNuclearOperator k p w f) 1
      = ∑ y : Fin d → kˣ,
          dworkTraceAdditiveCharacter k p
            (finitePolynomialEval k k f (fun i => (y i : k))) := by
  have hq : dworkQPow k p 1 = Nat.card k := by
    rw [dworkQPow, mul_one, FiniteField.pow_finrank_eq_natCard p k]
  have hsum : ∀ y : Fin d → kˣ,
      tateEval w (dworkIteratedSplittingProduct k p w f (Module.finrank (ZMod p) k))
          (fun i => ramifiedTeichmullerLift k p ((y i : k)))
        = dworkTraceAdditiveCharacter k p
            (finitePolynomialEval k k f (fun i => (y i : k))) := fun y =>
    tateEval_dworkIteratedSplittingProduct_teichmuller k p w f _ fun i => (y i).ne_zero
  rw [← Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => hsum y,
    sum_teichmullerTorus_tateEval k p w
      (dworkIteratedSplittingProduct k p w f (Module.finrank (ZMod p) k)),
    dworkTracePower_eq_splittingSum]
  congr 1
  refine tsum_congr fun u => ?_
  rw [dworkSplittingDiagonal]
  simp only [PNat.one_coe]
  rw [hq, mul_one]
end FirstPowerCharacterSum
end FiniteFields.Dwork
end
end
section
noncomputable section
open Filter Topology
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
attribute [local instance] dw5cResiduePrimeAlgebra
variable {d : ℕ} (w : PositiveMonomialWeight d)
section AuxiliaryVariable
omit [Fact p.Prime] [CharP k p] [Finite k] in
private theorem finsuppCons_injective :
    Function.Injective (fun u : MonomialIndex d => Finsupp.cons 1 u) := by
  intro u v huv
  have := congrArg Finsupp.tail huv
  rwa [Finsupp.tail_cons, Finsupp.tail_cons] at this
omit [Fact p.Prime] [CharP k p] [Finite k] in
theorem finitePolynomialEval_dworkAuxiliaryPolynomial (A : Type*) [CommRing A] [Algebra k A]
    (f : MonomialIndex d →₀ k) (x₀ : A) (x : Fin d → A) :
    finitePolynomialEval k A (dworkAuxiliaryPolynomial (k := k) f) (Fin.cons x₀ x)
      = x₀ * finitePolynomialEval k A f x := by
  rw [dworkAuxiliaryPolynomial, finitePolynomialEval, finitePolynomialEval,
    Finsupp.sum_mapDomain_index_inj finsuppCons_injective, Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  show algebraMap k A (f u) * ∏ i : Fin (d + 1), Fin.cons x₀ x i ^ (Finsupp.cons 1 u) i
      = x₀ * (algebraMap k A (f u) * ∏ i : Fin d, x i ^ u i)
  rw [Fin.prod_univ_succ]
  simp only [Finsupp.cons_zero, Finsupp.cons_succ, Fin.cons_zero, Fin.cons_succ, pow_one]
  ring
omit [Fact p.Prime] [CharP k p] [Finite k] in
theorem dworkAuxiliaryPolynomial_mapRange {K : Type*} [Field K] (σ : k →+* K)
    (f : MonomialIndex d →₀ k) :
    Finsupp.mapRange σ (map_zero σ) (dworkAuxiliaryPolynomial (k := k) f)
      = dworkAuxiliaryPolynomial (k := K) (Finsupp.mapRange σ (map_zero σ) f) := by
  rw [dworkAuxiliaryPolynomial, dworkAuxiliaryPolynomial]
  exact (Finsupp.mapDomain_mapRange _ _ _ (map_zero σ) (fun a b => map_add σ a b)).symm
end AuxiliaryVariable
section TorusReindex
omit [Fact p.Prime] [Field k] [CharP k p] [Finite k] in
theorem sum_units_pi_succ {M : Type*} [AddCommMonoid M] (K : Type*) [Field K] [Fintype K]
    [DecidableEq K] (F : (Fin (d + 1) → K) → M) :
    ∑ z : Fin (d + 1) → Kˣ, F (fun i => ((z i : K)))
      = ∑ x : {x : Fin d → K // ∀ i, x i ≠ 0},
          ∑ x₀ ∈ Finset.univ.erase (0 : K), F (Fin.cons x₀ (x : Fin d → K)) := by
  classical
  set torusEquiv : (Fin d → Kˣ) ≃ {x : Fin d → K // ∀ i, x i ≠ 0} :=
    (Equiv.piCongrRight fun _ : Fin d => (unitsEquivNeZero (G₀ := K))).trans
      (Equiv.subtypePiEquivPi (p := fun (_ : Fin d) (b : K) => b ≠ 0)).symm with htorus
  have hval : ∀ z' : Fin d → Kˣ,
      ((torusEquiv z' : {x : Fin d → K // ∀ i, x i ≠ 0}) : Fin d → K)
        = fun i => ((z' i : K)) := fun z' => rfl
  have hsplit : ∑ z : Fin (d + 1) → Kˣ, F (fun i => ((z i : K)))
      = ∑ z₀ : Kˣ, ∑ z' : Fin d → Kˣ,
          F (Fin.cons ((z₀ : K)) (fun i => ((z' i : K)))) := by
    rw [← Fintype.sum_prod_type (f := fun q : Kˣ × (Fin d → Kˣ) =>
      F (Fin.cons ((q.1 : K)) (fun i => ((q.2 i : K)))))]
    refine (Fintype.sum_equiv (consPiEquiv Kˣ d).symm _ _ fun q => ?_).symm
    show F (Fin.cons ((q.1 : K)) (fun i => ((q.2 i : K))))
      = F (fun i => (((consPiEquiv Kˣ d).symm q i : Kˣ) : K))
    congr 1
    exact (Fin.comp_cons (fun u : Kˣ => (u : K)) q.1 q.2).symm
  rw [hsplit, Finset.sum_comm]
  refine Fintype.sum_equiv torusEquiv _ _ fun z' => ?_
  rw [hval z']
  refine Eq.trans (Fintype.sum_equiv (unitsEquivNeZero (G₀ := K)) _
    (fun a : {z : K // z ≠ 0} => F (Fin.cons ((a : K)) (fun i => ((z' i : K)))))
    fun z₀ => rfl) ?_
  exact (Finset.sum_subtype (p := fun z : K => z ≠ 0) (Finset.univ.erase (0 : K))
    (fun z => by simp) (fun x₀ => F (Fin.cons x₀ (fun i => ((z' i : K)))))).symm
end TorusReindex
end FiniteFields.Dwork
end
end
section
noncomputable section
open Filter Topology
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
attribute [local instance] dw5cResiduePrimeAlgebra
variable {d : ℕ} (w : PositiveMonomialWeight d)
section Terminal
variable (k₀ : Type) [Field k₀] [CharP k₀ p] [Finite k₀]
attribute [local instance] dw4eExtensionCharP
omit [Finite k₀] in
theorem finitePolynomialEval_residueBaseChange (K : Type*) [Field K] [Algebra k₀ K]
    (f : MonomialIndex d →₀ k₀) (x : Fin d → K) :
    finitePolynomialEval K K (Finsupp.mapRange (algebraMap k₀ K) (map_zero _) f) x
      = finitePolynomialEval k₀ K f x := by
  classical
  rw [finitePolynomialEval_eq_sum, finitePolynomialEval_eq_sum,
    Finsupp.support_mapRange_of_injective (map_zero _) f (algebraMap k₀ K).injective]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finsupp.mapRange_apply]
  simp
theorem dworkTracePower_eq_toricPointCount (f : MonomialIndex d →₀ k₀)
    (w' : PositiveMonomialWeight (d + 1)) (n : ℕ)
    [Fintype (FiniteFields.Extension k₀ p n)]
    [DecidableEq (FiniteFields.Extension k₀ p n)] :
    ((Nat.card k₀ ^ (n + 1) : ℕ) : DworkCyclotomicField k₀ p)
        * (toricHypersurfacePointCount k₀ p f n : DworkCyclotomicField k₀ p)
      = ((Nat.card k₀ ^ (n + 1) - 1 : ℕ) : DworkCyclotomicField k₀ p) ^ d
        + ((Nat.card k₀ ^ (n + 1) - 1 : ℕ) : DworkCyclotomicField k₀ p) ^ (d + 1)
          * NuclearOperator.tracePower w'
              (dworkQFrobeniusNuclearOperator k₀ p w' (dworkAuxiliaryPolynomial (k := k₀) f))
              ⟨n + 1, Nat.succ_pos n⟩ := by
  classical
  set K := FiniteFields.Extension k₀ p n with hKdef
  have hcard : Nat.card K = Nat.card k₀ ^ (n + 1) := FiniteFields.natCard_extension k₀ p n
  have hfin : @Module.finrank (ZMod p) K _ _
        (@Algebra.toModule (ZMod p) K _ _ (dw5cResiduePrimeAlgebra K p))
      = Module.finrank (ZMod p) k₀ * (n + 1) := by
    have hmod : (@Algebra.toModule (ZMod p) K _ _ (dw5cResiduePrimeAlgebra K p))
        = (@Algebra.toModule (ZMod p) K _ _
            (FiniteField.instAlgebraZModExtension k₀ p (n + 1))) :=
      congrArg _ (Subsingleton.elim _ _)
    rw [hmod, mul_comm]
    exact finrank_zmod_extension_eq k₀ p n
  refine (dworkCyclotomicBaseChange k₀ p K).injective ?_
  rw [map_mul, map_natCast, map_natCast, map_add, map_pow, map_natCast, map_mul, map_pow,
    map_natCast, dworkCyclotomicBaseChange_tracePower k₀ p w' K
      (dworkAuxiliaryPolynomial (k := k₀) f) ⟨n + 1, Nat.succ_pos n⟩ hfin, ← hcard]
  have hchar := dworkTracePower_one_eq_characterSum K p w'
    (residueBaseChange (k := k₀) (K := K) (dworkAuxiliaryPolynomial (k := k₀) f))
  rw [hchar, sum_units_pi_succ K (fun z : Fin (d + 1) → K =>
    dworkTraceAdditiveCharacter K p
      (finitePolynomialEval K K
        (residueBaseChange (k := k₀) (K := K) (dworkAuxiliaryPolynomial (k := k₀) f)) z))]
  have hinner : ∀ x : {x : Fin d → K // ∀ i, x i ≠ 0},
      ∑ x₀ ∈ Finset.univ.erase (0 : K),
          dworkTraceAdditiveCharacter K p
            (finitePolynomialEval K K
              (residueBaseChange (k := k₀) (K := K) (dworkAuxiliaryPolynomial (k := k₀) f))
              (Fin.cons x₀ (x : Fin d → K)))
        = ∑ x₀ ∈ Finset.univ.erase (0 : K),
            dworkTraceAdditiveCharacter K p
              (x₀ * finitePolynomialEval k₀ K f (x : Fin d → K)) := by
    intro x
    refine Finset.sum_congr rfl fun x₀ _ => ?_
    rw [residueBaseChange, dworkAuxiliaryPolynomial_mapRange,
      finitePolynomialEval_dworkAuxiliaryPolynomial, finitePolynomialEval_residueBaseChange]
  rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => hinner x, hcard]
  exact toricHypersurfacePointCount_eq_characterSum k₀ p f n
end Terminal
end FiniteFields.Dwork
end
end
open Filter Topology
open FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
attribute [local instance] dw5cResiduePrimeAlgebra
variable {d : ℕ} (w : PositiveMonomialWeight d)
variable (k₀ : Type) [Field k₀] [CharP k₀ p] [Finite k₀]
attribute [local instance] dw4eExtensionCharP
theorem solution (f : MonomialIndex d →₀ k₀)
    (w' : PositiveMonomialWeight (d + 1)) (n : ℕ) :
    ((Nat.card k₀ ^ (n + 1) - 1 : ℕ) : DworkCyclotomicField k₀ p) ^ (d + 1)
        * NuclearOperator.tracePower w'
            (dworkQFrobeniusNuclearOperator k₀ p w' (dworkAuxiliaryPolynomial (k := k₀) f))
            ⟨n + 1, Nat.succ_pos n⟩
      = ((Nat.card k₀ ^ (n + 1) : ℕ) : DworkCyclotomicField k₀ p)
          * (toricHypersurfacePointCount k₀ p f n : DworkCyclotomicField k₀ p)
        - ((Nat.card k₀ ^ (n + 1) - 1 : ℕ) : DworkCyclotomicField k₀ p) ^ d := by
  letI := Fintype.ofFinite (FiniteFields.Extension k₀ p n)
  letI := Classical.decEq (FiniteFields.Extension k₀ p n)
  rw [dworkTracePower_eq_toricPointCount p k₀ f w' n]
  ring
