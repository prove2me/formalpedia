-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.inter_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:21.191214+00:00
-- url     : https://prove2.me/submissions/1bab7f5b-8e43-4ca8-aeb5-c27c960c3933

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_ex
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_tube

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HenselRootsBounded
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.HenselRootsBounded
theorem _root_.solution (h : Ctx K R ϖ) {a : K} (ha : ∀ k : ℕ, a ∈ Pk R ϖ k) : a = 0 := by
  have := h.t2
  have := h.red
  have h1 : ∀ x : K, a * x ∈ R := by
    intro x
    obtain ⟨b, hb⟩ := Pk_ex h x
    have := Pk_mul (ha b) hb
    rw [add_neg_cancel] at this
    exact Pk_zero.1 this
  by_contra hne
  have hsq : a * a ≠ 0 := by
    intro h0
    exact hne (by simpa using (pow_eq_zero_iff (n := 2) (by norm_num)).1 (by rw [sq]; exact h0))
  have hW : ({a * a}ᶜ : Set K) ∈ 𝓝 (0 : K) :=
    isOpen_compl_singleton.mem_nhds (by simpa using hsq.symm)
  obtain ⟨V, hV, hVR⟩ := tube h hW
  obtain ⟨V', hV', hsub⟩ := exists_nhds_half_neg hV
  have hmem : ∀ n : ℕ, (n : K) * a ∈ R := fun n => by rw [mul_comm]; exact h1 _
  obtain ⟨p, _, hp⟩ := h.isCompact.exists_mapClusterPt (f := atTop) (u := fun n : ℕ => (n : K) * a)
    (by
      rw [le_principal_iff, mem_map]
      exact Filter.univ_mem' hmem)
  have hU : {q : K | q - p ∈ V'} ∈ 𝓝 p := by
    have hc : Continuous fun q : K => q - p := continuous_id.sub continuous_const
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hV')
  have hf := hp.frequently hU
  obtain ⟨n, _, hn⟩ := (frequently_atTop.1 hf) 0
  obtain ⟨n', hn', hn2⟩ := (frequently_atTop.1 hf) (n + 1)
  have hd : ((n' - n : ℕ) : K) * a ∈ V := by
    have := hsub _ hn2 _ hn
    rw [Nat.cast_sub (by omega)]
    convert this using 1; ring
  obtain ⟨w, hw⟩ := h.nat (n' - n) (by omega)
  have := hVR _ hd (a * ((w⁻¹ : Kˣ) : K)) (h1 _)
  apply this
  rw [← hw]
  show (w : K) * a * (a * ((w⁻¹ : Kˣ) : K)) = a * a
  have : (w : K) * ((w⁻¹ : Kˣ) : K) = 1 := by simp
  calc (w : K) * a * (a * ((w⁻¹ : Kˣ) : K)) = a * a * ((w : K) * ((w⁻¹ : Kˣ) : K)) := by ring
    _ = a * a := by rw [this, mul_one]
end Formalism.FourierDecayAlt.P.HenselRootsBounded
