-- Prove2me | solution 1 for AutomorphicForm.sum_slotFamilyCoeff_mul_prod_eq_prod_of_isOrbitalIntegral_heckeWord_of_isOrbitalIntegral_sum_coeff_univWord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/1247aa06-c317-55db-98aa-8ce194dc411d

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Theorems.Thm_AutomorphicForm_exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_of_isRegularSemisimple_of_field
import Theorems.Thm_AutomorphicForm_eq_of_isOrbitalIntegral_of_isOrbitalIntegral_of_measure_preimage_localIntegralSet_eq_one
import Theorems.Thm_AutomorphicForm_isLocalTestFn_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_sum_slotFamilyCoeff_mul_prod_eq_prod_of_isOrbitalIntegral_heckeWord_of_isOrbitalIntegral_sum_coeff_univWord
p2m_attr_erase "instance" "LanglandsTunnell.CubicInduction.countable_GL2 LanglandsTunnell.CubicInduction.countable_mirabolicIndex"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.rightTranslationEmbed_smul_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.WindingDatum.mk.injEq AutomorphicForm.WindingDatum.mk.sizeOf_spec LanglandsTunnell.CubicInduction.coe_diagUnits2 NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero"
p2m_attr_erase "simp" "LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq LanglandsTunnell.RankinSelberg.mem_primeFibre LanglandsTunnell.CubicInduction.coe_diagUnitGL2 LanglandsTunnell.CubicInduction.iotaTorusLocal_zero LanglandsTunnell.CubicInduction.upperUnipotent3_zero LanglandsTunnell.CubicInduction.radicalP21_coe LanglandsTunnell.CubicInduction.coe_iotaGL LanglandsTunnell.CubicInduction.radicalP12_coe LanglandsTunnell.CubicInduction.radicalP12_zero LanglandsTunnell.CubicInduction.radicalP21_zero LanglandsTunnell.CubicInduction.upperUnipotent3_coe"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

namespace SLOTOI

open AutomorphicForm

theorem isLocalTestFn_finset_sum (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → GL (Fin 2) (v.adicCompletion K) → ℂ)
    (h : ∀ i ∈ s, IsLocalTestFn K v (g i)) : IsLocalTestFn K v (fun x => ∑ i ∈ s, g i x) := by
  induction s using Finset.induction_on with
  | empty => simpa using isLocalTestFn_zero K v
  | @insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    simp only [Finset.sum_insert ha]
    exact ⟨h1.1.comp₂ h2.1 (· + ·), h1.2.add h2.2⟩

theorem isLocalTestFn_const_mul (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (c : ℂ) (h : IsLocalTestFn K v f) :
    IsLocalTestFn K v (fun x => c * f x) :=
  ⟨h.1.comp (fun y : ℂ => c * y), h.2.comp_left (g := fun y : ℂ => c * y) (mul_zero _)⟩

theorem exists_bound_of_isLocalTestFn (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (h : IsLocalTestFn K v f) : ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C := by
  obtain ⟨C, hC⟩ := (h.2.isCompact_range h.1.continuous).isBounded.exists_norm_le
  exact ⟨C, fun g => hC _ (Set.mem_range_self g)⟩

theorem linear (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : IsRegularSemisimple γ)
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v γ) τ)
    (n : ℕ) (rK : Fin n → GL (Fin 2) (v.adicCompletion K)) (zK : GL (Fin 2) (v.adicCompletion K))
    {R : Type*} [DecidableEq R] (s : Finset R) (c : R → ℂ) (a b : R → ℕ) :
    ∃ J : R → ℂ,
      (∀ r ∈ s, IsOrbitalIntegral K v γ τ
        (fun x : GL (Fin 2) (v.adicCompletion K) =>
          ∑ ι : Fin (a r) → Fin n, (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
            (((List.ofFn fun i => rK (ι i)).prod * zK ^ (b r))⁻¹ * x)) (J r)) ∧
      IsOrbitalIntegral K v γ τ
        (fun x : GL (Fin 2) (v.adicCompletion K) => ∑ r ∈ s, c r *
          ∑ ι : Fin (a r) → Fin n, (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
            (((List.ofFn fun i => rK (ι i)).prod * zK ^ (b r))⁻¹ * x)) (∑ r ∈ s, c r * J r) := by
  classical
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := glBorelOf (v.adicCompletion K)
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion K)) := borelSpace_glBorelOf _
  haveI := isHaarMeasure_localHaar K v

  set W : R → GL (Fin 2) (v.adicCompletion K) → ℂ := fun r x =>
    ∑ ι : Fin (a r) → Fin n, (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
      (((List.ofFn fun i => rK (ι i)).prod * zK ^ (b r))⁻¹ * x) with hWdef
  have hW : ∀ r, IsLocalTestFn K v (W r) := fun r =>
    AutomorphicForm.isLocalTestFn_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul K v n rK zK (a r) (b r)
  set F : GL (Fin 2) (v.adicCompletion K) → ℂ := fun x => ∑ r ∈ s, W r x with hFdef
  have hF : IsLocalTestFn K v F := isLocalTestFn_finset_sum K v s W fun r _ => hW r
  obtain ⟨⟨w, hw, hwc⟩, -⟩ :=
    AutomorphicForm.exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_of_isRegularSemisimple_of_field
      (v.adicCompletion K) (localHaar K v) (isHaarMeasure_localHaar K v) γ hγ τ hτ F
      hF.1.continuous.measurable hF.2 (exists_bound_of_isLocalTestFn K v F hF)

  have hWnat : ∀ r y, ∃ k : ℕ, W r y = k := by
    intro r y
    refine ⟨(Finset.univ.filter fun ι : Fin (a r) → Fin n =>
      ((List.ofFn fun i => rK (ι i)).prod * zK ^ (b r))⁻¹ * y ∈ localIntegralSet K v).card, ?_⟩
    simp only [hWdef, Set.indicator_apply]
    rw [Finset.sum_boole]
  have hsupp : ∀ y, F y = 0 → ∀ r ∈ s, W r y = 0 := by
    intro y hy r hr
    choose k hk using fun r => hWnat r y
    have hsum : ((∑ r ∈ s, k r : ℕ) : ℂ) = 0 := by
      rw [Nat.cast_sum]
      have hy' := hy
      simp only [hFdef] at hy'
      simpa only [hk] using hy'
    have hk0 : k r = 0 := Finset.sum_eq_zero_iff.mp (by exact_mod_cast hsum) r hr
    rw [hk r, hk0, Nat.cast_zero]
  have hsecW : ∀ r ∈ s, IsSectionFn K v γ τ (W r) w := fun r hr =>
    ⟨hw.1, hw.2.1, hw.2.2.1, fun x hx => hw.2.2.2 x fun h0 => hx (hsupp _ h0 r hr)⟩
  have hsecC : IsSectionFn K v γ τ (fun x => ∑ r ∈ s, c r * W r x) w := by
    refine ⟨hw.1, hw.2.1, hw.2.2.1, fun x hx => hw.2.2.2 x fun h0 => hx ?_⟩
    exact Finset.sum_eq_zero fun r hr => by rw [hsupp _ h0 r hr, mul_zero]

  have hwi : Integrable (fun x => (w x : ℂ)) (localHaar K v) :=
    (Complex.continuous_ofReal.comp hwc).integrable_of_hasCompactSupport
      (hw.2.2.1.comp_left (g := fun t : ℝ => (t : ℂ)) Complex.ofReal_zero)
  have hconj : Continuous fun x : GL (Fin 2) (v.adicCompletion K) => x⁻¹ * γ * x := by fun_prop
  have hint : ∀ r, Integrable (fun x => W r (x⁻¹ * γ * x) * (w x : ℂ)) (localHaar K v) := by
    intro r
    obtain ⟨C, hC⟩ := exists_bound_of_isLocalTestFn K v (W r) (hW r)
    exact hwi.bdd_mul ((hW r).1.continuous.comp hconj).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hC _)
  refine ⟨fun r => ∫ x, W r (x⁻¹ * γ * x) * (w x : ℂ) ∂(localHaar K v),
    fun r hr => ⟨w, hsecW r hr, rfl⟩, ⟨w, hsecC, ?_⟩⟩
  simp only [Finset.sum_mul]
  rw [integral_finsetSum _ fun r _ => (hint r).const_mul (c r) |>.congr ?_]
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  · exact Filter.Eventually.of_forall fun x => by ring

end SLOTOI

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
    (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K))
    (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K))
    (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
    (γ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K))
    (hγ : ∀ v ∈ T, AutomorphicForm.IsRegularSemisimple (γ v))
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (AutomorphicForm.localCentralizer K v (γ v)) (AutomorphicForm.localCentralizerBorel K v (γ v)))
    (hτ : ∀ v ∈ T, @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (γ v)) (τ v))
    (hτ1 : ∀ v ∈ T, τ v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (IW : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIW : ∀ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T,
      ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
        AutomorphicForm.IsOrbitalIntegral K v (γ v) (τ v) (fun x : GL (Fin 2) (v.adicCompletion K) =>
            ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
              (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (m v hv) 1)⁻¹ * x)) (IW m v))
    (IT : HeightOneSpectrum (𝓞 K) → ℂ)
    (hIT : ∀ v ∈ T, AutomorphicForm.IsOrbitalIntegral K v (γ v) (τ v) (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ r ∈ (AutomorphicForm.SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).support,
          (AutomorphicForm.SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).coeff r *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) / (Ideal.absNorm (ws v).1.asIdeal : ℂ) ^ (js v) *
            ∑ ι : Fin (r 0) → Fin (nKs v),
              (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (r 1))⁻¹ * x)) (IT v)) :
    ∑ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T,
        AutomorphicForm.SatakeCombination.slotFamilyCoeff K L ws ks js T m * ∏ v ∈ T, IW m v =
      ∏ v ∈ T, IT v := by
  classical

  have key : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T), ∃ J : (Fin 2 →₀ ℕ) → ℂ,
      (∀ r ∈ (AutomorphicForm.SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).support,
        AutomorphicForm.IsOrbitalIntegral K v (γ v) (τ v)
          (fun x : GL (Fin 2) (v.adicCompletion K) =>
            ∑ ι : Fin (r 0) → Fin (nKs v), (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
              (((List.ofFn fun i => rKs v (ι i)).prod * zKs v ^ (r 1))⁻¹ * x)) (J r)) ∧
      AutomorphicForm.IsOrbitalIntegral K v (γ v) (τ v) (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ r ∈ (AutomorphicForm.SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).support,
          (AutomorphicForm.SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).coeff r *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) / (Ideal.absNorm (ws v).1.asIdeal : ℂ) ^ (js v) *
            ∑ ι : Fin (r 0) → Fin (nKs v),
              (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (r 1))⁻¹ * x))
        (∑ r ∈ (AutomorphicForm.SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).support,
          ((AutomorphicForm.SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).coeff r *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) / (Ideal.absNorm (ws v).1.asIdeal : ℂ) ^ (js v)) * J r) :=
    fun v hv => SLOTOI.linear K v (γ v) (hγ v hv) (τ v) (hτ v hv) (nKs v) (rKs v) (zKs v) _ _ (fun r : Fin 2 →₀ ℕ => r 0) (fun r : Fin 2 →₀ ℕ => r 1)
  choose J hJ using key

  have eIW : ∀ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T, ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      IW m v = J v hv (m v hv) := by
    intro m hm v hv
    have hmv : m v hv ∈ (AutomorphicForm.SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).support := by
      unfold AutomorphicForm.SatakeCombination.slotIndex AutomorphicForm.SatakeCombination.slotWord
        AutomorphicForm.SatakeCombination.slotDeg at hm
      exact Finset.mem_pi.mp hm v hv
    exact AutomorphicForm.eq_of_isOrbitalIntegral_of_isOrbitalIntegral_of_measure_preimage_localIntegralSet_eq_one K v (γ v) (hγ v hv) (τ v) (τ v) (hτ v hv) (hτ v hv) (hτ1 v hv) (hτ1 v hv) _
      (AutomorphicForm.isLocalTestFn_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul K v (nKs v) (rKs v) (zKs v) ((m v hv) 0) ((m v hv) 1))
      _ _ (hIW m hm v hv) ((hJ v hv).1 _ hmv)
  have eIT : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      IT v = ∑ r ∈ (AutomorphicForm.SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).support,
          ((AutomorphicForm.SatakeCombination.univWord (v.asIdeal.inertiaDeg' (ws v).1.asIdeal - 1) (ks v) (js v)).coeff r *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) / (Ideal.absNorm (ws v).1.asIdeal : ℂ) ^ (js v)) * J v hv r := by
    intro v hv
    refine AutomorphicForm.eq_of_isOrbitalIntegral_of_isOrbitalIntegral_of_measure_preimage_localIntegralSet_eq_one K v (γ v) (hγ v hv) (τ v) (τ v) (hτ v hv) (hτ v hv) (hτ1 v hv) (hτ1 v hv) _ ?_
      _ _ (hIT v hv) (hJ v hv).2
    exact SLOTOI.isLocalTestFn_finset_sum K v _ _ fun r _ => SLOTOI.isLocalTestFn_const_mul K v _ _
      (AutomorphicForm.isLocalTestFn_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul K v (nKs v) (rKs v) (zKs v) (r 0) (r 1))

  set J' : HeightOneSpectrum (𝓞 K) → (Fin 2 →₀ ℕ) → ℂ := fun v r => if hv : v ∈ T then J v hv r else 0 with hJ'
  have eJ' : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T) (r : Fin 2 →₀ ℕ), J' v r = J v hv r := fun v hv r => by
    simp [hJ', hv]
  calc ∑ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T,
          AutomorphicForm.SatakeCombination.slotFamilyCoeff K L ws ks js T m * ∏ v ∈ T, IW m v
      = ∑ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T,
          ∏ v ∈ T.attach, (AutomorphicForm.SatakeCombination.slotCoeff K L ws v.1 (ks v.1) (js v.1) (m v.1 v.2) *
            J' v.1 (m v.1 v.2)) := by
        refine Finset.sum_congr rfl fun m hm => ?_
        unfold AutomorphicForm.SatakeCombination.slotFamilyCoeff
        rw [Finset.prod_mul_distrib, ← Finset.prod_attach T (fun v => IW m v)]
        congr 1
        exact Finset.prod_congr rfl fun v _ => by rw [eIW m hm v.1 v.2, eJ' v.1 v.2]
    _ = ∏ v ∈ T, ∑ r ∈ (AutomorphicForm.SatakeCombination.slotWord K L ws v (ks v) (js v)).support,
          AutomorphicForm.SatakeCombination.slotCoeff K L ws v (ks v) (js v) r * J' v r := by
        unfold AutomorphicForm.SatakeCombination.slotIndex
        rw [Finset.prod_sum]
    _ = ∏ v ∈ T, IT v := by
        refine Finset.prod_congr rfl fun v hv => ?_
        rw [eIT v hv]
        unfold AutomorphicForm.SatakeCombination.slotCoeff AutomorphicForm.SatakeCombination.slotWord
          AutomorphicForm.SatakeCombination.slotDeg
        exact Finset.sum_congr rfl fun r _ => by rw [eJ' v hv r]

end S_AutomorphicForm_sum_slotFamilyCoeff_mul_prod_eq_prod_of_isOrbitalIntegral_heckeWord_of_isOrbitalIntegral_sum_coeff_univWord
end P2MW
export P2MW.S_AutomorphicForm_sum_slotFamilyCoeff_mul_prod_eq_prod_of_isOrbitalIntegral_heckeWord_of_isOrbitalIntegral_sum_coeff_univWord (solution)
