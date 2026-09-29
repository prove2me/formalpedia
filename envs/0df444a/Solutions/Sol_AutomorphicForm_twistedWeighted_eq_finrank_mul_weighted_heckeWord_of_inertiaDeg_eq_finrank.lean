-- Prove2me | solution 1 for AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/7ccae695-f8a6-5529-90fd-d255129d1ab0

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_LocalLanglands_HeckeCosetSystem

import Theorems.Thm_AutomorphicForm_SatakeCombination_sum_twistedShell_heckeWord_eq_mul_sum_shell_baseChange_of_two_mul_eq
import Theorems.Thm_AutomorphicForm_SatakeCombination_sum_twistedShell_heckeWord_eq_mul_sum_shell_baseChange_of_lt
import Theorems.Thm_AutomorphicForm_integral_twistedConj_map_algEquiv_mul_weight_eq_integral_unipotentGL2_of_biInvariant
import Theorems.Thm_AutomorphicForm_measureReal_norm_eq_and_norm_algEquiv_sub_mul_eq_of_prod_eq_of_ramificationIdx_eq_one
import Theorems.Thm_AutomorphicForm_norm_algEquiv_sub_mul_eq_norm_mul_max_of_norm_ne_one
import Theorems.Thm_AutomorphicForm_exists_algEquiv_mulEquiv_semiLocalComponent_localEmbed_eq_of_subsingleton_extension

import Theorems.Thm_AutomorphicForm_integral_heckeWord_twistedConj_mul_weight_eq_two_mul_log_mul_twistedShellValue
import Theorems.Thm_AutomorphicForm_eq_two_mul_log_mul_shellValue_of_isWeightedOrbitalIntegral_baseChange_heckeWord
import Theorems.Thm_AutomorphicForm_exists_norm_eq_zpow_and_norm_eq_zpow_of_prod_algEquiv_pow_eq
import Theorems.Thm_AutomorphicForm_exists_norm_one_sub_mul_inv_eq_zpow_neg_of_ne
import Theorems.Thm_AutomorphicForm_SatakeCombination_twistedShellValue_eq_mul_shellValue

import Theorems.Thm_AutomorphicForm_isLocalTestFn_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul

import Theorems.Thm_LocalGL2_sum_indicator_word_inv_mul_scalar_mul_unipotentGL2_mem_localIntegralSet_eq_walkCount

import Theorems.Thm_AutomorphicForm_eq_two_mul_log_mul_sum_of_isWeightedOrbitalIntegral_diagUnits2_of_biInvariant
import Theorems.Thm_AutomorphicForm_twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_prime
import Theorems.Thm_LocalGL2_mem_doubleCoset_diagPi_zpow_mul_localRepInf_zpow_iff_of_upperTriangular
import Theorems.Thm_LocalGL2_sum_indicator_integralSubgroup_ofFn_prod_inv_mul_eq_walkCount_of_mem_doubleCoset_zpow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_finrank

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

namespace P2mWInert

theorem subsingleton_extension_of_inertiaDeg_eq_finrank
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w₀ : v.Extension (𝓞 L))
    (hinert : v.asIdeal.inertiaDeg' w₀.1.asIdeal = Module.finrank K L) :
    Subsingleton (v.Extension (𝓞 L)) := by
  classical
  haveI := v.isMaximal
  have hp0 : v.asIdeal ≠ ⊥ := v.ne_bot

  have hlies : ∀ w : v.Extension (𝓞 L), w.1.asIdeal.LiesOver v.asIdeal := fun w =>
    ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩
  have hmem : ∀ w : v.Extension (𝓞 L), w.1.asIdeal ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 L) := fun w =>
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mpr ⟨w.1.isPrime, hlies w⟩
  have hsum := Ideal.sum_ramification_inertia (𝓞 L) K L (p := v.asIdeal) hp0

  have key : ∀ P ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 L), P = w₀.1.asIdeal := by
    intro P hP
    by_contra hne
    have hPe : P ∈ (IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 L)).erase w₀.1.asIdeal :=
      Finset.mem_erase.2 ⟨hne, hP⟩
    have h1 := Finset.add_sum_erase (IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 L))
      (fun P : Ideal (𝓞 L) => v.asIdeal.ramificationIdx' P * v.asIdeal.inertiaDeg' P) (hmem w₀)
    have h2 := Finset.add_sum_erase ((IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 L)).erase w₀.1.asIdeal)
      (fun P : Ideal (𝓞 L) => v.asIdeal.ramificationIdx' P * v.asIdeal.inertiaDeg' P) hPe
    haveI : P.IsPrime := ((IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp hP).1
    haveI : P.LiesOver v.asIdeal := ((IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp hP).2
    haveI := hlies w₀
    haveI := w₀.1.isPrime
    have he0 : 0 < v.asIdeal.ramificationIdx' w₀.1.asIdeal :=
      Nat.pos_iff_ne_zero.mpr (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver _ hp0)
    have heP : 0 < v.asIdeal.ramificationIdx' P :=
      Nat.pos_iff_ne_zero.mpr (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver _ hp0)
    have hfP : 0 < v.asIdeal.inertiaDeg' P := Nat.pos_iff_ne_zero.mpr (Ideal.inertiaDeg_ne_zero _ _)
    have hA : Module.finrank K L ≤ v.asIdeal.ramificationIdx' w₀.1.asIdeal * v.asIdeal.inertiaDeg' w₀.1.asIdeal := by
      rw [hinert]; exact Nat.le_mul_of_pos_left _ he0
    have hB : 1 ≤ v.asIdeal.ramificationIdx' P * v.asIdeal.inertiaDeg' P := Right.one_le_mul heP hfP
    omega
  constructor
  intro w₁ w₂
  have h₁ := key _ (hmem w₁)
  have h₂ := key _ (hmem w₂)
  exact Subtype.ext (HeightOneSpectrum.ext (h₁.trans h₂.symm))

def walk (R : ℕ) : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => (R + 1) * walk R n 1
  | n + 1, s + 1 => walk R n s + R * walk R n (s + 2)

theorem walk_zero_zero (R : ℕ) : walk R 0 0 = 1 := by rw [walk]
theorem walk_zero_succ (R s : ℕ) : walk R 0 (s + 1) = 0 := by rw [walk]
theorem walk_succ_zero (R n : ℕ) : walk R (n + 1) 0 = (R + 1) * walk R n 1 := by rw [walk]
theorem walk_succ_succ (R n s : ℕ) : walk R (n + 1) (s + 1) = walk R n s + R * walk R n (s + 2) := by rw [walk]

section NormString

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

noncomputable abbrev sigmaUnits : (L ⊗[K] A)ˣ →* (L ⊗[K] A)ˣ :=
  Units.map (AutomorphicForm.sigmaTensor K L A σ).toMonoidHom

theorem sigmaGL_diagUnits2 (x y : (L ⊗[K] A)ˣ) :
    AutomorphicForm.sigmaGL K L A σ (diagUnits2 x y) =
      diagUnits2 (sigmaUnits K L A σ x) (sigmaUnits K L A σ y) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change AutomorphicForm.sigmaTensor K L A σ ((diagUnits2 x y : GL (Fin 2) (L ⊗[K] A)) i j) = _
  fin_cases i <;> fin_cases j <;>
    simp [LanglandsTunnell.CubicInduction.coe_diagUnits2]

theorem sigmaGL_iterate_diagUnits2 (i : ℕ) (x y : (L ⊗[K] A)ˣ) :
    (⇑(AutomorphicForm.sigmaGL K L A σ))^[i] (diagUnits2 x y) =
      diagUnits2 ((⇑(sigmaUnits K L A σ))^[i] x) ((⇑(sigmaUnits K L A σ))^[i] y) := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, sigmaGL_diagUnits2, Function.iterate_succ_apply',
        Function.iterate_succ_apply']

theorem diagUnits2_mul (x y x' y' : (L ⊗[K] A)ˣ) :
    diagUnits2 x y * diagUnits2 x' y' = diagUnits2 (x * x') (y * y') := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul]
  fin_cases i <;> fin_cases j <;>
    simp [LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.mul_apply, Fin.sum_univ_two]

theorem diagUnits2_one : (diagUnits2 1 1 : GL (Fin 2) (L ⊗[K] A)) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [LanglandsTunnell.CubicInduction.coe_diagUnits2]

theorem list_prod_map_diagUnits2 (n : ℕ) (f g : ℕ → (L ⊗[K] A)ˣ) :
    ((List.range n).map fun i => diagUnits2 (f i) (g i)).prod =
      diagUnits2 (∏ i ∈ Finset.range n, f i) (∏ i ∈ Finset.range n, g i) := by
  induction n with
  | zero => simp [diagUnits2_one]
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih, List.map_singleton, List.prod_singleton,
        diagUnits2_mul, Finset.prod_range_succ, Finset.prod_range_succ]

noncomputable def unitNorm (u : (L ⊗[K] A)ˣ) : (L ⊗[K] A)ˣ :=
  ∏ i ∈ Finset.range (Module.finrank K L), (⇑(sigmaUnits K L A σ))^[i] u

theorem normString_diagUnits2 (x y : (L ⊗[K] A)ˣ) :
    AutomorphicForm.normString K L A σ (diagUnits2 x y) =
      diagUnits2 (unitNorm K L A σ x) (unitNorm K L A σ y) := by
  unfold AutomorphicForm.normString unitNorm
  rw [show ((List.range (Module.finrank K L)).map fun i =>
        (⇑(AutomorphicForm.sigmaGL K L A σ))^[i] (diagUnits2 x y)) =
      (List.range (Module.finrank K L)).map fun i =>
        diagUnits2 ((⇑(sigmaUnits K L A σ))^[i] x) ((⇑(sigmaUnits K L A σ))^[i] y) from
      List.map_congr_left fun i _ => sigmaGL_iterate_diagUnits2 K L A σ i x y,
    list_prod_map_diagUnits2]

theorem unitNorm_mul (u u' : (L ⊗[K] A)ˣ) :
    unitNorm K L A σ (u * u') = unitNorm K L A σ u * unitNorm K L A σ u' := by
  unfold unitNorm
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => iterate_map_mul (sigmaUnits K L A σ) i u u'

theorem unitNorm_one : unitNorm K L A σ 1 = 1 := by
  unfold unitNorm
  exact Finset.prod_eq_one fun i _ => iterate_map_one (sigmaUnits K L A σ) i

theorem unitNorm_inv (u : (L ⊗[K] A)ˣ) : unitNorm K L A σ u⁻¹ = (unitNorm K L A σ u)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← unitNorm_mul, inv_mul_cancel, unitNorm_one]

theorem coe_iterate_sigmaUnits (i : ℕ) (u : (L ⊗[K] A)ˣ) :
    (((⇑(sigmaUnits K L A σ))^[i] u : (L ⊗[K] A)ˣ) : L ⊗[K] A) =
      (⇑(AutomorphicForm.sigmaTensor K L A σ))^[i] (u : L ⊗[K] A) := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl

theorem coe_unitNorm (u : (L ⊗[K] A)ˣ) :
    ((unitNorm K L A σ u : (L ⊗[K] A)ˣ) : L ⊗[K] A) =
      ∏ i ∈ Finset.range (Module.finrank K L), (⇑(AutomorphicForm.sigmaTensor K L A σ))^[i] (u : L ⊗[K] A) := by
  unfold unitNorm
  rw [Units.coe_prod]
  exact Finset.prod_congr rfl fun i _ => coe_iterate_sigmaUnits K L A σ i u

theorem toTensorGL_diagUnits2 (a b : Aˣ) :
    AutomorphicForm.toTensorGL K L A (diagUnits2 a b) =
      diagUnits2 (Units.map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toMonoidHom a)
        (Units.map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toMonoidHom b) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)
      ((diagUnits2 a b : GL (Fin 2) A) i j) = _
  fin_cases i <;> fin_cases j <;>
    simp [LanglandsTunnell.CubicInduction.coe_diagUnits2]

theorem diagUnits2_injective {x y x' y' : (L ⊗[K] A)ˣ} (h : diagUnits2 x y = diagUnits2 x' y') :
    x = x' ∧ y = y' := by
  have h00 := congrArg (fun g : GL (Fin 2) (L ⊗[K] A) => (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0) h
  have h11 := congrArg (fun g : GL (Fin 2) (L ⊗[K] A) => (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1) h
  simp only [LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h00 h11
  exact ⟨Units.ext h00, Units.ext h11⟩

theorem prod_iterate_sigmaTensor_div_eq (α β : (L ⊗[K] A)ˣ) (a b : Aˣ)
    (hN : AutomorphicForm.normString K L A σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L A (diagUnits2 a b)) :
    ∏ i ∈ Finset.range (Module.finrank K L),
        (⇑(AutomorphicForm.sigmaTensor K L A σ))^[i] ((β * α⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) =
      (1 : L) ⊗ₜ[K] ((b * a⁻¹ : Aˣ) : A) := by
  rw [normString_diagUnits2, toTensorGL_diagUnits2] at hN
  obtain ⟨hα, hβ⟩ := diagUnits2_injective K L A hN
  rw [← coe_unitNorm, unitNorm_mul, unitNorm_inv, hα, hβ, ← map_inv, ← map_mul]
  rfl

theorem prod_iterate_sigmaTensor_eq (α β : (L ⊗[K] A)ˣ) (a b : Aˣ)
    (hN : AutomorphicForm.normString K L A σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L A (diagUnits2 a b)) :
    (∏ i ∈ Finset.range (Module.finrank K L),
        (⇑(AutomorphicForm.sigmaTensor K L A σ))^[i] (α : L ⊗[K] A) = (1 : L) ⊗ₜ[K] (a : A)) ∧
    (∏ i ∈ Finset.range (Module.finrank K L),
        (⇑(AutomorphicForm.sigmaTensor K L A σ))^[i] (β : L ⊗[K] A) = (1 : L) ⊗ₜ[K] (b : A)) := by
  rw [normString_diagUnits2, toTensorGL_diagUnits2] at hN
  obtain ⟨hα, hβ⟩ := diagUnits2_injective K L A hN
  refine ⟨?_, ?_⟩
  · rw [← coe_unitNorm, hα]; rfl
  · rw [← coe_unitNorm, hβ]; rfl

end NormString

section ThetaPhi

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
  (Φ : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
  (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
  (hΦσ : ∀ x : L ⊗[K] v.adicCompletion K, Φ (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ x) = θ (Φ x))

include hΦσ in
theorem theta_pow_Phi (i : ℕ) (x : L ⊗[K] v.adicCompletion K) :
    (θ ^ i) (Φ x) = Φ ((⇑(AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ))^[i] x) := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply, ← ih, pow_succ, AlgEquiv.mul_apply, hΦσ]

include hΦσ in

theorem prod_theta_pow_Phi_eq
    (hΦbase : ∀ t : v.adicCompletion K,
      Φ ((1 : L) ⊗ₜ[K] t) = algebraMap (v.adicCompletion K) (w.1.adicCompletion L) t)
    (n : ℕ) (x : L ⊗[K] v.adicCompletion K) (a : v.adicCompletion K)
    (hx : ∏ i ∈ Finset.range n, (⇑(AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ))^[i] x =
      (1 : L) ⊗ₜ[K] a) :
    ∏ i ∈ Finset.range n, (θ ^ i) (Φ x) = algebraMap (v.adicCompletion K) (w.1.adicCompletion L) a := by
  simp_rw [theta_pow_Phi K L σ v w Φ θ hΦσ]
  rw [← map_prod, hx, hΦbase]

end ThetaPhi

open AutomorphicForm

theorem heckeWord_semiLocal_eq_comp_symm
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (e : GL (Fin 2) (w.1.adicCompletion L) ≃* GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hemb : ∀ g : GL (Fin 2) (w.1.adicCompletion L),
      semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w.1 g) = e g)
    (hint : e '' localIntegralSet L w.1 = semiLocalIntegralSet K L v)
    (k n : ℕ) (rL : Fin n → GL (Fin 2) (w.1.adicCompletion L)) (z : GL (Fin 2) (w.1.adicCompletion L)) (j : ℕ) :
    (fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
        ∑ ι : Fin k → Fin n, (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
          ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w.1
            ((List.ofFn fun m => rL (ι m)).prod * z ^ j)))⁻¹ * x)) =
      (fun y : GL (Fin 2) (w.1.adicCompletion L) =>
        ∑ ι : Fin k → Fin n, (localIntegralSet L w.1).indicator (fun _ => (1 : ℂ))
          (((List.ofFn fun m => rL (ι m)).prod * z ^ j)⁻¹ * y)) ∘ e.symm := by
  funext x
  simp only [Function.comp_apply]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [hemb]
  have key : ∀ g : GL (Fin 2) (w.1.adicCompletion L),
      (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) (e g) =
        (localIntegralSet L w.1).indicator (fun _ => (1 : ℂ)) g := by
    intro g
    by_cases hg : g ∈ localIntegralSet L w.1
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem]
      rw [← hint]; exact ⟨g, hg, rfl⟩
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem]
      rw [← hint]; rintro ⟨g', hg', hgg'⟩
      exact hg (e.injective hgg' ▸ hg')
  have hx : (e ((List.ofFn fun m => rL (ι m)).prod * z ^ j))⁻¹ * x =
      e ((((List.ofFn fun m => rL (ι m)).prod * z ^ j))⁻¹ * e.symm x) := by
    rw [map_mul e _ (e.symm x), map_inv, MulEquiv.apply_symm_apply]
  rw [hx, key]

theorem exists_addHaar_integers_eq_one (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))
    [MeasurableSpace (w.adicCompletion L)] [BorelSpace (w.adicCompletion L)] :
    ∃ μE : Measure (w.adicCompletion L),
      μE.IsAddHaarMeasure ∧ μE (w.adicCompletionIntegers L : Set (w.adicCompletion L)) = 1 := by
  have hc : IsCompact (w.adicCompletionIntegers L : Set (w.adicCompletion L)) :=
    isCompact_iff_compactSpace.2 (AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 L) L w)
  have ho : IsOpen (w.adicCompletionIntegers L : Set (w.adicCompletion L)) :=
    (AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 L) L).out w
  let K₀ : TopologicalSpace.PositiveCompacts (w.adicCompletion L) :=
    { carrier := (w.adicCompletionIntegers L : Set (w.adicCompletion L))
      isCompact' := hc
      interior_nonempty' := by
        rw [ho.interior_eq]; exact ⟨0, (w.adicCompletionIntegers L).zero_mem⟩ }
  refine ⟨Measure.addHaarMeasure K₀, Measure.isAddHaarMeasure_addHaarMeasure K₀, ?_⟩
  exact Measure.addHaarMeasure_self

theorem exists_norm_eq_absNorm_inv (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    ∃ ϖ : v.adicCompletion K, ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  obtain ⟨x, hx⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v (WithZero.exp (-1))
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hx
    exact WithZero.coe_ne_zero hx.symm
  have hv0 : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
  have hk : ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (Multiplicative.toAdd (WithZero.unzero hv0)) := by
    rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv0]
    push_cast
    rfl
  have hexp : (Valued.v x : WithZero (Multiplicative ℤ)) = WithZero.exp (Multiplicative.toAdd (WithZero.unzero hv0)) := by
    conv_lhs => rw [← WithZero.coe_unzero hv0]
    rfl
  have hm1 : Multiplicative.toAdd (WithZero.unzero hv0) = -1 :=
    WithZero.exp_injective (hexp.symm.trans hx)
  refine ⟨x, ?_⟩
  rw [hk, hm1, zpow_neg, zpow_one]

theorem sigmaCentralizer_map_eq_map_centralizer
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (e : GL (Fin 2) (w.1.adicCompletion L) ≃* GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hσθ : ∀ x : GL (Fin 2) (w.1.adicCompletion L),
      sigmaGL K L (v.adicCompletion K) σ (e x) = e (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x))
    (hbase : ∀ g : GL (Fin 2) (v.adicCompletion K),
      toTensorGL K L (v.adicCompletion K) g =
        e (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)) g))
    (γ : GL (Fin 2) (v.adicCompletion K)) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (δ' : GL (Fin 2) (w.1.adicCompletion L)) (hδ' : e δ' = δ)
    (hT : twistedCentralizer K L (v.adicCompletion K) σ δ =
      (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))).map (toTensorGL K L (v.adicCompletion K))) :
    sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) δ' =
      (localCentralizer K v γ).map
        (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletion K) (w.1.adicCompletion L))) := by
  ext t'
  rw [mem_sigmaCentralizer_iff, Subgroup.mem_map]
  have h1 : t' * δ' * (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom t')⁻¹ = δ' ↔
      e t' ∈ twistedCentralizer K L (v.adicCompletion K) σ δ := by
    rw [twistedCentralizer, mem_sigmaCentralizer_iff, ← e.injective.eq_iff, map_mul, map_mul, map_inv, hδ', hσθ]
  rw [h1, hT, Subgroup.mem_map]
  constructor
  · rintro ⟨s, hs, hst⟩
    refine ⟨s, hs, ?_⟩
    apply e.injective
    rw [← hbase, hst]
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, hbase s⟩

end P2mWInert

open AutomorphicForm in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)

    (ws : ∀ u : HeightOneSpectrum (𝓞 K), u.Extension (𝓞 L))
    (hinert : v.asIdeal.inertiaDeg' (ws v).1.asIdeal = Module.finrank K L)
    (ϖ : (ws v).1.adicCompletionIntegers L) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) ϖ ≠ 0)
    (n : ℕ) (rL : Fin n → GL (Fin 2) ((ws v).1.adicCompletion L))
    (hrL : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
      (LocalGL2.diagPi ϖ hϖ0) rL)
    (z : GL (Fin 2) ((ws v).1.adicCompletion L))
    (hz : (z : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
      algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) ϖ •
        (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)))

    (ϖK : v.adicCompletionIntegers K) (hϖK : Irreducible ϖK)
    (hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0)
    (nK : ℕ) (rK : Fin nK → GL (Fin 2) (v.adicCompletion K))
    (hrK : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (LocalGL2.diagPi ϖK hϖK0) rK)
    (zK : GL (Fin 2) (v.adicCompletion K))
    (hzK : (zK : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (k j : ℕ)

    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b)
    (α β : (L ⊗[K] v.adicCompletion K)ˣ)
    (hN : AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b))
    (τ : @Measure (AutomorphicForm.localCentralizer K v (diagUnits2 a b))
      (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)) τ)
    (hτ1 : τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} = 1)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)))
    (hτ' : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ')
    (hτ'1 : τ' {t | (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈
      AutomorphicForm.semiLocalIntegralSet K L v} = 1)
    (J J' : ℂ)
    (hJ : AutomorphicForm.IsWeightedOrbitalIntegral K v (diagUnits2 a b) τ
      (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ e ∈ (SatakeCombination.slotWord K L ws v k j).support,
          SatakeCombination.slotCoeff K L ws v k j e *
            ∑ ι : Fin (e 0) → Fin nK,
              (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rK (ι m)).prod * zK ^ (e 1))⁻¹ * x))
      J)
    (hJ' : AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ'
      (fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
        ∑ ι : Fin k → Fin n,
          (AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
            ((AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
              ((List.ofFn fun m => rL (ι m)).prod * z ^ j)))⁻¹ * x))
      J') :
    J' = (Module.finrank K L : ℂ) * J := by
  classical

  have hsub : Subsingleton (v.Extension (𝓞 L)) :=
    P2mWInert.subsingleton_extension_of_inertiaDeg_eq_finrank K L v (ws v) hinert

  obtain ⟨Φ, e, θ, heΦ, hΦσ, hΦbase, hΦint, hθ, hfin, hw, hres, hemb, hint, hσθ, hbase, hwt, htrans, hHaar, hcont, hcont'⟩ :=
    AutomorphicForm.exists_algEquiv_mulEquiv_semiLocalComponent_localEmbed_eq_of_subsingleton_extension
      K L hprime σ hσ v hv hsub (ws v)

  set α' : ((ws v).1.adicCompletion L)ˣ := Units.map Φ.toRingEquiv.toRingHom.toMonoidHom α with hα'
  set β' : ((ws v).1.adicCompletion L)ˣ := Units.map Φ.toRingEquiv.toRingHom.toMonoidHom β with hβ'
  have hδ' : e (diagUnits2 α' β') = diagUnits2 α β := by
    refine Matrix.GeneralLinearGroup.ext fun p q => ?_
    rw [heΦ]
    fin_cases p <;> fin_cases q <;>
      simp [LanglandsTunnell.CubicInduction.coe_diagUnits2, hα', hβ']
  have hδ'' : e.symm (diagUnits2 α β) = diagUnits2 α' β' := by
    rw [← hδ', MulEquiv.symm_apply_apply]

  obtain ⟨hNa, hNb⟩ := P2mWInert.prod_iterate_sigmaTensor_eq K L (v.adicCompletion K) σ α β a b hN
  have hNα' : ∏ i ∈ Finset.range (Module.finrank K L), (θ ^ i) (α' : (ws v).1.adicCompletion L) =
      algebraMap (v.adicCompletion K) ((ws v).1.adicCompletion L) a :=
    P2mWInert.prod_theta_pow_Phi_eq K L σ v (ws v) Φ θ hΦσ hΦbase _ _ _ hNa
  have hNβ' : ∏ i ∈ Finset.range (Module.finrank K L), (θ ^ i) (β' : (ws v).1.adicCompletion L) =
      algebraMap (v.adicCompletion K) ((ws v).1.adicCompletion L) b :=
    P2mWInert.prod_theta_pow_Phi_eq K L σ v (ws v) Φ θ hΦσ hΦbase _ _ _ hNb

  haveI := hτ'
  have pack : ∀ δE : GL (Fin 2) ((ws v).1.adicCompletion L), e.symm (diagUnits2 α β) = δE →
      ∃ (τE : @Measure (sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) δE) (borel _))
        (sE : GL (Fin 2) ((ws v).1.adicCompletion L) → ℝ),
        @Measure.IsHaarMeasure _ _ _ (borel _) τE ∧
        τE {t | (t : GL (Fin 2) ((ws v).1.adicCompletion L)) ∈ localIntegralSet L (ws v).1} = 1 ∧
        (∀ y, 0 ≤ sE y) ∧ Measurable[localGLBorel L (ws v).1] sE ∧ HasCompactSupport sE ∧
        (∀ y : GL (Fin 2) ((ws v).1.adicCompletion L),
          (fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin k → Fin n, (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
              ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                ((List.ofFn fun m => rL (ι m)).prod * z ^ j)))⁻¹ * x))
            (e (y⁻¹ * δE * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom y)) ≠ 0 →
            ∫ t : sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) δE,
                sE ((t : GL (Fin 2) ((ws v).1.adicCompletion L)) * y) ∂τE = 1) ∧
        J' = ∫ y : GL (Fin 2) ((ws v).1.adicCompletion L),
            (fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              ∑ ι : Fin k → Fin n, (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rL (ι m)).prod * z ^ j)))⁻¹ * x))
              (e (y⁻¹ * δE * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom y)) *
              ((LocalWeight.weight y : ℝ) : ℂ) * (sE y : ℂ) ∂(localHaar L (ws v).1) := by
    intro δE hδE
    subst hδE
    exact htrans (diagUnits2 α β) τ' hτ' hτ'1 _ J' hJ'
  obtain ⟨τE, sE, hτE, hτE1, hsE0, hsEm, hsEc, hsE1, hJ'E⟩ := pack (diagUnits2 α' β') hδ''

  set Φw : GL (Fin 2) ((ws v).1.adicCompletion L) → ℂ := fun y =>
    ∑ ι : Fin k → Fin n, (localIntegralSet L (ws v).1).indicator (fun _ => (1 : ℂ))
      (((List.ofFn fun m => rL (ι m)).prod * z ^ j)⁻¹ * y) with hΦw
  have hG1 := P2mWInert.heckeWord_semiLocal_eq_comp_symm K L v (ws v) e hemb hint k n rL z j
  have hker : ∀ g : GL (Fin 2) ((ws v).1.adicCompletion L),
      (fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
        ∑ ι : Fin k → Fin n, (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
          ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
            ((List.ofFn fun m => rL (ι m)).prod * z ^ j)))⁻¹ * x)) (e g) = Φw g := by
    intro g
    rw [hG1, Function.comp_apply, MulEquiv.symm_apply_apply]

  have hJ'loc : J' = ∫ y : GL (Fin 2) ((ws v).1.adicCompletion L),
      Φw (y⁻¹ * diagUnits2 α' β' * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom y) *
        ((LocalWeight.weight y : ℝ) : ℂ) * (sE y : ℂ) ∂(localHaar L (ws v).1) := by
    rw [hJ'E]
    simp_rw [hker]
  have hsE1' : ∀ y : GL (Fin 2) ((ws v).1.adicCompletion L),
      Φw (y⁻¹ * diagUnits2 α' β' * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom y) ≠ 0 →
        ∫ t : sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α' β'),
            sE ((t : GL (Fin 2) ((ws v).1.adicCompletion L)) * y) ∂τE = 1 := by
    intro y hy
    have h := hsE1 y
    simp_rw [hker] at h
    exact h hy

  have hT' : sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α' β') =
      (localCentralizer K v (diagUnits2 a b)).map
        (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletion K) ((ws v).1.adicCompletion L))) := by
    exact P2mWInert.sigmaCentralizer_map_eq_map_centralizer K L σ v (ws v) e θ hσθ hbase (diagUnits2 a b)
      (diagUnits2 α β) (diagUnits2 α' β') hδ'
      (AutomorphicForm.twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_prime
        K L hprime σ hσ (v.adicCompletion K) a b hab α β hN)

  have hNα'' : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) ((ws v).1.adicCompletion L)),
      (θ ^ i) (α' : (ws v).1.adicCompletion L) = algebraMap (v.adicCompletion K) ((ws v).1.adicCompletion L) a := by
    rw [hfin]; exact hNα'
  have hNβ'' : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) ((ws v).1.adicCompletion L)),
      (θ ^ i) (β' : (ws v).1.adicCompletion L) = algebraMap (v.adicCompletion K) ((ws v).1.adicCompletion L) b := by
    rw [hfin]; exact hNβ'
  obtain ⟨ra, hα, ha⟩ := AutomorphicForm.exists_norm_eq_zpow_and_norm_eq_zpow_of_prod_algEquiv_pow_eq
    K L v (ws v) hw θ α' a hNα''
  obtain ⟨rb, hβ, hb⟩ := AutomorphicForm.exists_norm_eq_zpow_and_norm_eq_zpow_of_prod_algEquiv_pow_eq
    K L v (ws v) hw θ β' b hNβ''
  rw [hfin] at ha hb
  obtain ⟨d, hd0⟩ := AutomorphicForm.exists_norm_one_sub_mul_inv_eq_zpow_neg_of_ne K v a b hab
  have hd : ra = rb → ‖1 - ((b * a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-(d : ℤ)) := fun h => hd0 (by rw [ha, hb, h])

  have hprimew : (Module.finrank (v.adicCompletion K) ((ws v).1.adicCompletion L)).Prime := by
    rw [hfin]; exact hprime
  set q : ℕ := Ideal.absNorm v.asIdeal with hq
  set ℓ : ℕ := Module.finrank K L with hℓ
  set Wq : ℕ → ℕ → ℕ := P2mWInert.walk q with hWq
  set WQ : ℕ → ℕ → ℕ := P2mWInert.walk (q ^ ℓ) with hWQ
  set φ : ℤ → ℕ → ℂ := fun a' s' => if 2 * a' + s' = (k : ℤ) + 2 * j then (WQ k s' : ℂ) else 0 with hφ
  set f : ℤ → ℕ → ℂ := fun a' s' =>
    ∑ e ∈ (AutomorphicForm.SatakeCombination.univWord (ℓ - 1) k j).support,
      (AutomorphicForm.SatakeCombination.univWord (ℓ - 1) k j).coeff e * (q : ℂ) ^ (e 1) / (q : ℂ) ^ (ℓ * j) *
        (if 2 * a' + s' = (e 0 : ℤ) + 2 * (e 1 : ℤ) then (Wq (e 0) s' : ℂ) else 0) with hf
  set P : ℕ → ℂ := fun i => if i = 0 then 1 else if i ≤ d then
      ((q : ℂ) ^ ((ℓ - 1) * (i - 1)) * ∑ t ∈ Finset.range ℓ, (q : ℂ) ^ t)⁻¹ else 0 with hP
  have hP0 : P 0 = 1 := by simp [hP]
  have hP1 : ∀ i : ℕ, 1 ≤ i → i ≤ d →
      P i = ((q : ℂ) ^ ((ℓ - 1) * (i - 1)) * ∑ t ∈ Finset.range ℓ, (q : ℂ) ^ t)⁻¹ := by
    intro i h1 h2
    have hi : i ≠ 0 := by omega
    simp [hP, hi, h2]
  have hPd : ∀ i : ℕ, d < i → P i = 0 := by
    intro i hi
    have h1 : i ≠ 0 := by omega
    have h2 : ¬ i ≤ d := by omega
    simp [hP, h1, h2]

  have hA := AutomorphicForm.integral_heckeWord_twistedConj_mul_weight_eq_two_mul_log_mul_twistedShellValue
    K L v (ws v) hw hprimew θ hθ hres ϖ hϖ hϖ0 n rL hrL z hz k j a b hab α' β' hNα'' hNβ'' hT' ra rb hα hβ d hd
    τE hτE hτE1 sE hsE0 hsEm hsEc hsE1'
    WQ (P2mWInert.walk_zero_zero _) (P2mWInert.walk_zero_succ _)
      (by rw [hfin]; exact P2mWInert.walk_succ_zero _) (by rw [hfin]; exact P2mWInert.walk_succ_succ _)
    φ (fun _ _ => rfl) P hP0 (by rw [hfin]; exact hP1) hPd
  rw [hfin] at hA

  have hB := AutomorphicForm.eq_two_mul_log_mul_shellValue_of_isWeightedOrbitalIntegral_baseChange_heckeWord
    K L v ws hinert ϖK hϖK hϖK0 nK rK hrK zK hzK k j a b hab τ hτ hτ1 J hJ ra rb ha hb d hd
    Wq (P2mWInert.walk_zero_zero _) (P2mWInert.walk_zero_succ _) (P2mWInert.walk_succ_zero _)
      (P2mWInert.walk_succ_succ _)
    f (fun _ _ => rfl)

  have hD := AutomorphicForm.SatakeCombination.twistedShellValue_eq_mul_shellValue
    q ℓ (Nat.one_le_iff_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot |> fun h => by
        simpa [hq] using h))
      (hℓ ▸ Module.finrank_pos) Wq (P2mWInert.walk_zero_zero _) (P2mWInert.walk_zero_succ _)
      (P2mWInert.walk_succ_zero _) (P2mWInert.walk_succ_succ _)
    WQ (P2mWInert.walk_zero_zero _) (P2mWInert.walk_zero_succ _) (P2mWInert.walk_succ_zero _)
      (P2mWInert.walk_succ_succ _) k j φ (fun _ _ => rfl) f (fun _ _ => rfl) d P hP0 hP1 hPd ra rb

  rw [hJ'loc, hA, hD, hB]
  ring

end S_AutomorphicForm_twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_finrank
end P2MW
export P2MW.S_AutomorphicForm_twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_finrank (solution)
