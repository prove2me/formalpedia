-- Prove2me | solution 1 for FiniteFields.Dwork.dworkSplittingValue_frobeniusProduct
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T06:54:16.675699+00:00
-- url     : https://prove2.me/submissions/0b6f8ee9-8105-4e99-855a-80862dbf66a8

import Mathlib
import Definitions.Def_FiniteFields_Dwork_AdditiveCharacter
import Theorems.Thm_FiniteFields_Dwork_dworkPowerSeriesEval_rescale
section
noncomputable section
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k]
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
open Filter Function IsUltrametricDist Metric PowerSeries Set
open scoped NNReal Topology
namespace FiniteFields.Dwork
variable (k : Type*) [Field k]
variable (p : ℕ) [Fact p.Prime] [CharP k p] [Finite k]
theorem dworkArtinHasseEval_eq_tsum (x : DworkCyclotomicField k p) :
    dworkArtinHasseEval k p x =
      ∑' n : ℕ, PowerSeries.coeff n (dworkArtinHasseExponential k p) * x ^ n :=
  rfl
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
theorem val_prod {α : Type*} (s : Finset α) (f : α → DworkPrincipalUnit k p) :
    (∏ i ∈ s, f i).val = ∏ i ∈ s, (f i).val := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, DworkPrincipalUnit.val_one]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, DworkPrincipalUnit.val_mul, ih]
end DworkPrincipalUnit
theorem artinHasseWittUnit_zero : artinHasseWittUnit k p 0 = 1 := by
  rw [artinHasseWittUnit, map_zero]
  rfl
theorem artinHasseWittUnit_add (u v : WittVector p (CoefficientRing k p)) :
    artinHasseWittUnit k p (u + v) = artinHasseWittUnit k p u * artinHasseWittUnit k p v := by
  rw [artinHasseWittUnit, artinHasseWittUnit, artinHasseWittUnit, map_add]
  rfl
theorem artinHasseWittUnit_sum {α : Type*} (s : Finset α)
    (f : α → WittVector p (CoefficientRing k p)) :
    artinHasseWittUnit k p (∑ i ∈ s, f i) = ∏ i ∈ s, artinHasseWittUnit k p (f i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, artinHasseWittUnit_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, artinHasseWittUnit_add, ih]
theorem artinHasseWittHom_trace (w : CoefficientRing k p) :
    (Additive.toMul (artinHasseWittHom k p (wittTraceTeichmuller k p w))).val
      = ∏ i ∈ Finset.range (Module.finrank (ZMod p) k),
          (Additive.toMul (artinHasseWittHom k p
            (WittVector.teichmuller p ((frobeniusLift k p)^[i] w)))).val := by
  have h : artinHasseWittUnit k p (wittTraceTeichmuller k p w)
      = ∏ i ∈ Finset.range (Module.finrank (ZMod p) k),
          artinHasseWittUnit k p (WittVector.teichmuller p ((frobeniusLift k p)^[i] w)) := by
    rw [wittTraceTeichmuller, artinHasseWittUnit_sum]
  rw [← artinHasseWittUnit_apply, h, DworkPrincipalUnit.val_prod]
  rfl
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
omit [Finite k] in
theorem iterate_frobeniusLift_teichmullerLift (i : ℕ) (x : k) :
    (frobeniusLift k p)^[i] (teichmullerLift k p x) = teichmullerLift k p (x ^ p ^ i) := by
  induction i with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, frobeniusLift_teichmuller]
      congr 1
      rw [← pow_mul, pow_succ]
end FiniteFields.Dwork
end
end
open PowerSeries IsUltrametricDist
open FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
theorem solution (x : k) :
    (Additive.toMul (artinHasseWittHom k p
        (wittTraceTeichmuller k p (teichmullerLift k p x)))).val
      = dworkFrobeniusConjugateProduct k p x := by
  rw [artinHasseWittHom_trace, dworkFrobeniusConjugateProduct]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [iterate_frobeniusLift_teichmullerLift]
  exact artinHasseWittHom_teichmuller k p (x ^ p ^ i)
