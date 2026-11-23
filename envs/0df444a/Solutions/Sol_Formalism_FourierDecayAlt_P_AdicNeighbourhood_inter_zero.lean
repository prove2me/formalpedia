-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdicNeighbourhood.inter_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:34.128377+00:00
-- url     : https://prove2.me/submissions/300a0400-d7a7-47b2-9904-35ee71d874be

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdicNeighbourhood
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_small_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdicNeighbourhood
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.FourierDecayAlt.P.AdicNeighbourhood
theorem _root_.solution {R : Subring K} [T2Space K] [IsReduced K] (hc : IsCompact (R : Set K))
    (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) (ϖ : K) (hu : ∀ x : K, ∃ m : ℕ, ϖ ^ m * x ∈ R)
    (x : K) (hx : ∀ n, x ∈ I R (ϖ ^ n)) : x = 0 := by
  by_contra hx0
  have hx2 : x ^ 2 ≠ 0 := fun h => hx0 (IsNilpotent.eq_zero ⟨2, h⟩)
  have hI : ∀ y : K, y * x ∈ R := by
    intro y
    obtain ⟨m, hm⟩ := hu y
    obtain ⟨r, hr, e⟩ := hx m
    have : y * x = ϖ ^ m * y * r := by rw [e]; ring
    rw [this]; exact R.mul_mem hm hr
  have hW : ({x ^ 2}ᶜ : Set K) ∈ 𝓝 (0 : K) := isOpen_compl_singleton.mem_nhds (by
    simpa using hx2.symm)
  obtain ⟨U, hU, hUR⟩ := small_mul hc hW
  obtain ⟨U', hU', hsub⟩ := exists_nhds_half_neg hU
  obtain ⟨a, -, ha⟩ := hc.exists_mapClusterPt (f := (atTop : Filter ℕ)) (u := fun n : ℕ => (n : K) * x)
    (le_principal_iff.2 (mem_map.2 (Filter.univ_mem' fun n : ℕ => hI (n : K))))
  have hN : {y | y - a ∈ U'} ∈ 𝓝 a := by
    have : ContinuousAt (fun y : K => y - a) a := (continuous_id.sub continuous_const).continuousAt
    exact this.preimage_mem_nhds (by simpa using hU')
  have hf := frequently_atTop.1 (ha.frequently hN)
  obtain ⟨n, -, h1⟩ := hf 0
  obtain ⟨m, hm, h2⟩ := hf (n + 1)
  have h3 := hsub _ h2 _ h1
  obtain ⟨d, rfl⟩ : ∃ d, m = n + 1 + d := ⟨m - (n + 1), by omega⟩
  have e : ((n + 1 + d : ℕ) : K) * x - a - ((n : K) * x - a) = ((d + 1 : ℕ) : K) * x := by
    push_cast; ring
  rw [e] at h3
  obtain ⟨v, hv⟩ := hn (d + 1) (by omega)
  have h4 := hUR _ h3 _ (hI ((v⁻¹ : Kˣ) : K))
  apply h4
  show ((d + 1 : ℕ) : K) * x * (((v⁻¹ : Kˣ) : K) * x) = x ^ 2
  rw [← hv]
  have : (v : K) * ((v⁻¹ : Kˣ) : K) = 1 := by simp
  linear_combination x ^ 2 * this
end Formalism.FourierDecayAlt.P.AdicNeighbourhood
