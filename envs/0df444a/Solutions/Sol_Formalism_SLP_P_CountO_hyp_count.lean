-- Prove2me | solution 1 for Formalism.SLP.P.CountO.hyp_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:49:06.508853+00:00
-- url     : https://prove2.me/submissions/88427942-a3c0-48bf-bd02-c4f427897d79

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO
import Theorems.Thm_Formalism_SLP_P_CountO_exists_hom_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
open Formalism.SLP.P.CountO
variable {R : Type} [CommRing R] [IsDedekindDomain R]
namespace Formalism.SLP.P.CountO
theorem _root_.solution (P : Ideal R) [P.IsMaximal] [Finite (R ⧸ P)] {X : Type}
    [AddCommGroup X] [Module R X] (k : ℕ)
    (hhom : Finite (X →ₗ[R] R ⧸ P) ∧ Nat.card (X →ₗ[R] R ⧸ P) ≤ Nat.card (R ⧸ P) ^ k) :
    (hyp P X).Finite ∧ (hyp P X).ncard ≤ Nat.card (R ⧸ P) ^ k := by
  classical
  obtain ⟨hfin, hcard⟩ := hhom
  let F : Submodule R X → (X →ₗ[R] R ⧸ P) := fun L =>
    if h : L ∈ hyp P X then Classical.choose (exists_hom_ker P L h.1 h.2) else 0
  have hF : ∀ L ∈ hyp P X, LinearMap.ker (F L) = L := by
    intro L hL
    simp only [F, dif_pos hL]
    exact Classical.choose_spec (exists_hom_ker P L hL.1 hL.2)
  have hinj : Set.InjOn F (hyp P X) := by
    intro L₁ h₁ L₂ h₂ h
    rw [← hF L₁ h₁, ← hF L₂ h₂, h]
  have hfinS : (hyp P X).Finite := Set.Finite.of_finite_image (Set.toFinite _) hinj
  refine ⟨hfinS, ?_⟩
  calc (hyp P X).ncard ≤ (Set.univ : Set (X →ₗ[R] R ⧸ P)).ncard :=
        Set.ncard_le_ncard_of_injOn F (fun _ _ => Set.mem_univ _) hinj (Set.toFinite _)
    _ = Nat.card (X →ₗ[R] R ⧸ P) := Set.ncard_univ _
    _ ≤ _ := hcard
end Formalism.SLP.P.CountO
