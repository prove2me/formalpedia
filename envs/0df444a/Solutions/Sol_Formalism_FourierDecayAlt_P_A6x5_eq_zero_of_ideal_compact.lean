-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x5.eq_zero_of_ideal_compact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:32.478105+00:00
-- url     : https://prove2.me/submissions/fe7e66de-9267-4977-bd9f-a1c196ab1df5

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqZeroOfIdealCompact
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x5_multiples_near_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.DoubleCosetMeasures Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x5
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.FourierDecayAlt.P.A6x5
theorem _root_.solution [T2Space K] [IsReduced K] (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    (C : Set K) (hC : IsCompact C) (i : K) (hi : ∀ a : K, a * i ∈ C) : i = 0 := by
  set S : Set (K × K) := Set.range fun k : ℕ =>
    (((k + 1 : ℕ) : K) * i, Ring.inverse ((k + 1 : ℕ) : K) * i) with hS
  have hSC : S ⊆ C ×ˢ C := by
    rintro _ ⟨k, rfl⟩
    exact ⟨hi _, hi _⟩
  have hcl : closure S ⊆ C ×ˢ C := closure_minimal hSC (hC.prod hC).isClosed
  have hcc : IsCompact (closure S) := (hC.prod hC).of_isClosed_subset isClosed_closure hcl
  have hmul : closure S ⊆ {p : K × K | p.1 * p.2 = i ^ 2} := by
    refine closure_minimal ?_ (isClosed_eq (continuous_fst.mul continuous_snd) continuous_const)
    rintro _ ⟨k, rfl⟩
    change ((k + 1 : ℕ) : K) * i * (Ring.inverse ((k + 1 : ℕ) : K) * i) = i ^ 2
    have := Ring.mul_inverse_cancel _ (hn (k + 1) (by omega))
    calc ((k + 1 : ℕ) : K) * i * (Ring.inverse ((k + 1 : ℕ) : K) * i)
        = (((k + 1 : ℕ) : K) * Ring.inverse ((k + 1 : ℕ) : K)) * i ^ 2 := by ring
      _ = i ^ 2 := by rw [this, one_mul]
  have himg : Prod.fst '' closure S = closure (Prod.fst '' S) :=
    image_closure_of_isCompact hcc continuous_fst.continuousOn
  have h0 : (0 : K) ∈ closure (Prod.fst '' S) := by
    rw [mem_closure_iff_nhds]
    intro W hW
    obtain ⟨k, hk⟩ := multiples_near_zero C hC i hi W hW
    exact ⟨_, hk, ⟨_, ⟨k, rfl⟩, rfl⟩⟩
  rw [← himg] at h0
  obtain ⟨⟨x, y⟩, hp, hx⟩ := h0
  have h1 : x * y = i ^ 2 := hmul hp
  have hx' : x = 0 := hx
  rw [hx', zero_mul] at h1
  exact IsNilpotent.eq_zero ⟨2, h1.symm⟩
end Formalism.FourierDecayAlt.P.A6x5
