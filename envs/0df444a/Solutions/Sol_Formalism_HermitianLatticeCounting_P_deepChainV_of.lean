-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.deepChainV_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:54:55.228313+00:00
-- url     : https://prove2.me/submissions/feaf36d9-6f77-425e-a11a-73c274dd1843

import Definitions.Def_Formalism_FlagUnipotentLattices_CuspidalityThreshold
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_OperatorHilbertSchmidtNorm
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_CoefficientBoundLemmas_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory NumberField
open scoped ComplexOrder
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (HD : DeepChain) : DeepChainV := by
  intro C hC
  obtain ⟨C0, hC0, H⟩ := HD C hC
  refine ⟨C0 + C, by linarith, ?_⟩
  intro n q f rd g b τ₁ τs ρ Kxx Bs D volG volK hn hq hqn hf hrd hg hb hτ hττ hD hvK hvG hρ0 hρ hK hB hvol
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hY0 : 0 < Ydat n f rd g b := by unfold Ydat; positivity
  have hb10 : 0 ≤ b1 n q f b := by unfold b1; positivity
  set Y := Ydat n f rd g b
  set Z := Y ^ (C * (n : ℝ) ^ 2 * f) with hZ
  have hZ0 : 0 < Z := Real.rpow_pos_of_pos hY0 _
  have hvol' : volG / Z / volK ≤ (C * n * rd * g) ^ (n ^ 2 * f) := by
    have e : volG / Z / volK = volG / volK / Z := by ring
    rw [e]
    calc volG / volK / Z ≤ 1 := (div_le_one hZ0).mpr hvol
      _ ≤ _ := by
        apply one_le_pow₀
        calc (1:ℝ) = 1 * 1 * 1 * 1 := by ring
          _ ≤ C * n * rd * g := by gcongr
  have key := H n q f rd g b τ₁ τs ρ Kxx Bs D (volG / Z) volK hn hq hqn hf hrd hg hb hτ hττ hD hvK
    (by positivity) hρ0 hρ hK hB hvol'
  have hτs : 0 < τs := hτ.trans hττ
  have eY : Y ^ ((C0 + C) * (n : ℝ) ^ 2 * f) = Y ^ (C0 * (n : ℝ) ^ 2 * f) * Z := by
    rw [hZ, ← Real.rpow_add hY0]; congr 1; ring
  calc volG * Kxx = Z * (volG / Z * Kxx) := by field_simp
    _ ≤ Z * (D * Y ^ (C0 * (n : ℝ) ^ 2 * f)
          * (C0 * (n : ℝ) ^ 4 * (f : ℝ) ^ 2 * g * rd * b1 n q f b) ^ (16 * q * n ^ 2 * f)
          * τs ^ (12 * n ^ 2 * f)) := by gcongr
    _ = D * (Y ^ (C0 * (n : ℝ) ^ 2 * f) * Z)
          * (C0 * (n : ℝ) ^ 4 * (f : ℝ) ^ 2 * g * rd * b1 n q f b) ^ (16 * q * n ^ 2 * f)
          * τs ^ (12 * n ^ 2 * f) := by ring
    _ ≤ _ := by
      rw [eY]
      gcongr
      linarith
end Formalism.HermitianLatticeCounting.P
