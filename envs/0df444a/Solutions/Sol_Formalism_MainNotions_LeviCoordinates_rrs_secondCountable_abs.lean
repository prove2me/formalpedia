-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrs_secondCountable_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:09:37.255305+00:00
-- url     : https://prove2.me/submissions/b392f887-e042-4b43-9751-dee462aa8d1f

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrsSecondCountableAbs
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrs_cover
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Set Topology
open scoped Pointwise
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (μ : Measure G) [SigmaFinite μ] [μ.IsOpenPosMeasure] (U : ℕ → Set G)
    (hU : ∀ n, IsOpen (U n)) (h1 : ∀ n, (1 : G) ∈ U n) (hb : ∀ O ∈ 𝓝 (1 : G), ∃ n, U n ⊆ O) :
    SecondCountableTopology G := by
  classical
  choose S hSc hS using fun n => rrs_cover μ (hU n) (h1 n)
  let B : Set (Set G) := ⋃ n, (fun x => x • (U n * (U n)⁻¹)) '' S n
  have hBc : B.Countable := Set.countable_iUnion fun n => (hSc n).image _
  refine (TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_).secondCountableTopology hBc
  · intro s hs
    obtain ⟨n, x, -, rfl⟩ : ∃ n, ∃ x ∈ S n, x • (U n * (U n)⁻¹) = s := by simpa [B] using hs
    exact ((hU n).mul_right).smul x
  · intro a O haO hO
    have hO' : a⁻¹ • O ∈ 𝓝 (1 : G) :=
      (hO.smul a⁻¹).mem_nhds ⟨a, haO, by simp⟩
    obtain ⟨V₁, hV₁o, hV₁1, hV₁⟩ := exists_open_nhds_one_split hO'
    obtain ⟨V₂, hV₂o, hV₂1, hV₂⟩ := exists_open_nhds_one_split (hV₁o.mem_nhds hV₁1)
    have hW : V₂ ∩ V₂⁻¹ ∈ 𝓝 (1 : G) :=
      Filter.inter_mem (hV₂o.mem_nhds hV₂1) (hV₂o.inv.mem_nhds (by simpa using hV₂1))
    have hkey : ∀ p ∈ V₂ ∩ V₂⁻¹, ∀ q ∈ V₂ ∩ V₂⁻¹, ∀ r ∈ V₂ ∩ V₂⁻¹, ∀ s ∈ V₂ ∩ V₂⁻¹,
        a * (p * q⁻¹ * (r * s⁻¹)) ∈ O := by
      intro p hp q hq r hr s hs
      have h1' := hV₂ p hp.1 q⁻¹ (Set.mem_inv.1 hq.2)
      have h2' := hV₂ r hr.1 s⁻¹ (Set.mem_inv.1 hs.2)
      have h3 := hV₁ _ h1' _ h2'
      obtain ⟨o, ho, he⟩ := Set.mem_smul_set.1 h3
      rw [← he, smul_eq_mul, ← mul_assoc, mul_inv_cancel, one_mul]
      exact ho
    obtain ⟨n, hn⟩ := hb _ hW
    obtain ⟨x, hxS, hax⟩ := hS n a
    refine ⟨x • (U n * (U n)⁻¹), Set.mem_iUnion.2 ⟨n, x, hxS, rfl⟩, hax, ?_⟩
    obtain ⟨_, ⟨p, hp, q, hq, rfl⟩, rfl⟩ := hax
    rintro _ ⟨_, ⟨r, hr, s, hs, rfl⟩, rfl⟩
    have := hkey q⁻¹ (hn (Set.mem_inv.1 hq)) p (hn hp) r (hn hr) s⁻¹ (hn (Set.mem_inv.1 hs))
    convert this using 1
    simp only [smul_eq_mul, inv_inv]
    group
end Formalism.MainNotions.LeviCoordinates
