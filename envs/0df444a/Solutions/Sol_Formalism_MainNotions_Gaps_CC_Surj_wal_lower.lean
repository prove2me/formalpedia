-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.CC.Surj.wal_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:00:34.700139+00:00
-- url     : https://prove2.me/submissions/74a2223e-581c-4d1c-83c2-664c8476d372

import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ClassCountWaLat
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_P_adelstabL_den


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.CC Formalism.MainNotions.Gaps.CC.Surj
open Formalism.UG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : Type} [Fintype n] [DecidableEq n]
local notation "Av" => E ⊗[F] v.adicCompletion F
local notation "Sv" => Formalism.UG.P.lvS F E v
local notation "ιv" => inclE (F := F) (E := E) (v.adicCompletion F)
namespace Formalism.MainNotions.Gaps.CC.Surj
theorem _root_.solution (Λ : Submodule (𝓞 E) (n → E))
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ x : n → Av, (∀ i, x i ∈ Sv) →
      (fun i => (m : Av) * x i) ∈ latS (F := F) (v.adicCompletion F) Sv Λ := by
  classical
  have hk : ∀ k : n, ∃ N : ℕ, ∃ f : Fin N → E, ∃ w : Fin N → Λ,
      ∑ j, f j • (w j : n → E) = Pi.single k 1 := by
    intro k
    have : (Pi.single k 1 : n → E) ∈ Submodule.span E (Λ : Set (n → E)) := by
      rw [hspan]; exact Submodule.mem_top
    obtain ⟨N, f, w, h⟩ := Submodule.mem_span_set'.1 this
    exact ⟨N, f, fun j => ⟨w j, (w j).2⟩, h⟩
  choose N f w hw using hk
  obtain ⟨m, hm0, hm⟩ := Formalism.UG.P.adelstabL_den (fun p : Σ k : n, Fin (N k) => f p.1 p.2)
  have hsingle : ∀ k, (Pi.single k (m : E) : n → E) ∈ Λ := by
    intro k
    have : (Pi.single k (m : E) : n → E) =
        ∑ j, (⟨(m : E) * f k j, hm ⟨k, j⟩⟩ : 𝓞 E) • (w k j : n → E) := by
      have h1 : (Pi.single k (m : E) : n → E) = (m : E) • (Pi.single k 1 : n → E) := by
        rw [← Pi.single_smul', smul_eq_mul, mul_one]
      rw [h1, ← hw k, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← algebraMap_smul E, smul_smul]
      rfl
    rw [this]
    exact sum_mem fun j _ => Λ.smul_mem _ (w k j).2
  refine ⟨m, hm0, fun x hx => ?_⟩
  have hC : (m : Av) = ιv (m : E) := (map_intCast _ m).symm
  have : (fun i => (m : Av) * x i) =
      ∑ k, (⟨x k, hx k⟩ : Sv) • (fun i => ιv ((Pi.single k (m : E) : n → E) i)) := by
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · show _ = (_ : Sv) • ιv ((Pi.single i (m : E) : n → E) i)
      rw [Pi.single_eq_same, Subring.smul_def, smul_eq_mul, ← hC, mul_comm]
    · intro k _ hki
      show (_ : Sv) • ιv ((Pi.single k (m : E) : n → E) i) = 0
      rw [Pi.single_apply, if_neg (Ne.symm hki), map_zero, smul_zero]
    · exact fun h => absurd (Finset.mem_univ i) h
  rw [this]
  exact sum_mem fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hsingle k, rfl⟩)
end Formalism.MainNotions.Gaps.CC.Surj
