-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.folner_seq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:17:21.721355+00:00
-- url     : https://prove2.me/submissions/5dc8e5fd-ed62-4671-91cc-f0f5a81e6442

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerConv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerSum
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerLim
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolner
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_ratio_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution [LocallyCompactSpace G] [SecondCountableTopology G] {S : Set G} {μS : Measure G}
    (hS : IsHaarSub S μS) (hF : IsFolner S μS) :
    ∃ Ω : ℕ → Set G, (∀ n, MeasurableSet (Ω n) ∧ Ω n ⊆ S ∧ 0 < μS (Ω n) ∧ μS (Ω n) < ⊤) ∧
      ∀ K : Set G, IsCompact K → K ⊆ S →
        Tendsto (fun n => (μS {t | t ∈ Ω n ∧ ∀ k ∈ K, k * t ∈ Ω n}).toReal / (μS (Ω n)).toReal) atTop (𝓝 1) := by
  let Kx := CompactExhaustion.choice G
  have hε : ∀ n : ℕ, (0 : ℝ≥0∞) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) := fun n =>
    ENNReal.ofReal_pos.mpr (by positivity)
  choose Ω hΩm hΩS hpos hfin hle using fun n : ℕ =>
    hF (Kx n ∩ S) ((Kx.isCompact n).inter_right hS.1) Set.inter_subset_right _ (hε n)
  refine ⟨Ω, fun n => ⟨hΩm n, hΩS n, hpos n, hfin n⟩, ?_⟩
  intro K hK hKS
  obtain ⟨N, hN⟩ := Kx.exists_superset_of_isCompact hK
  have hlow : Tendsto (fun n : ℕ => 1 / (1 + 1 / ((n : ℝ) + 1))) atTop (𝓝 1) := by
    have h1 := tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
    have h2 : Tendsto (fun n : ℕ => (1 : ℝ) / (1 + 1 / ((n : ℝ) + 1))) atTop (𝓝 (1 / (1 + 0))) :=
      tendsto_const_nhds.div h1 (by norm_num)
    rwa [add_zero, div_one] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hsub : {t | t ∈ Ω n ∧ ∀ k ∈ Kx n ∩ S, k * t ∈ Ω n} ⊆ {t | t ∈ Ω n ∧ ∀ k ∈ K, k * t ∈ Ω n} :=
      fun t ht => ⟨ht.1, fun k hk => ht.2 k ⟨Kx.subset hn (hN hk), hKS hk⟩⟩
    have hAB := measure_mono (μ := μS) hsub
    have hBΩ : μS {t | t ∈ Ω n ∧ ∀ k ∈ K, k * t ∈ Ω n} ≤ μS (Ω n) := measure_mono (fun t ht => ht.1)
    have hBfin := (hBΩ.trans_lt (hfin n)).ne
    have hAfin := ((hAB.trans hBΩ).trans_lt (hfin n)).ne
    have hΩpos : 0 < (μS (Ω n)).toReal := ENNReal.toReal_pos (hpos n).ne' (hfin n).ne
    have hkey := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hAfin) (hle n)
    rw [ENNReal.toReal_mul, ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_one] at hkey
    have hAB' := ENNReal.toReal_mono hBfin hAB
    have hc : 0 < 1 + 1 / ((n : ℝ) + 1) := by positivity
    rw [div_le_div_iff₀ hc hΩpos]
    nlinarith [mul_le_mul_of_nonneg_left hAB' hc.le]
  · exact Filter.Eventually.of_forall fun n => ratio_le_one (fun t ht => ht.1) (hfin n)
end Formalism.L2.S.Pv.EnergyAbs
