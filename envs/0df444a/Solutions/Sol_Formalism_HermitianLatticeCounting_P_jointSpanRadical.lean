-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.jointSpanRadical
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:28.031455+00:00
-- url     : https://prove2.me/submissions/5ceee3ec-5609-45a0-8769-4e0cf6682115

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_swap0
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_le_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_X_iso
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pairing_isotropicSpan_lastVector
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_z_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pairing_lastVector_lastVector
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_lastVectorNotMemSup
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_finrank_Xa
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_finrank_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Dl_swap
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Dl_injL
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_isotropicSpan_le_jointSpan_left
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_isotropicSpan_le_jointSpan_right
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_lastVector_mem_jointSpan_left
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_lastVector_mem_jointSpan_right
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_jointSpan_eq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_z_ne_zero
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pairing_jointSpan_isotropicMeet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
namespace Formalism.HermitianLatticeCounting.P
section Base
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
private theorem HermSpace_B_add_right (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (x y z : V) : H.B x (y + z) = H.B x y + H.B x z :=
  map_add _ _ _
private theorem HermSpace_B_smul_right_eq_star_mul (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (c : K) (x y : V) : H.B x (c • y) = star c * H.B x y := by
  rw [LinearMap.map_smulₛₗ, smul_eq_mul, starRingEnd_apply]
end Base
section Base2
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
end Base2
section CaseA
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {H : HermSpace K V} {r : ℕ}
end CaseA
section Gram
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
end Gram
section V0
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
end V0
section Sig
variable {K U : Type} [Field K] [StarRing K] [AddCommGroup U] [Module K U]
end Sig
section Perp
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
end Perp
section DetBlocks
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
end DetBlocks
section Lift
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
end Lift
end Formalism.HermitianLatticeCounting.P
end

set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.JointSpanRadical := by
  intro K V _ _ _ _ _ H r F F' j hj c hA' hb hb' hI hI' hz hD
  have hJ := jointSpan_eq F F' hz
  have hmI : Formalism.HermitianLatticeCounting.S6.II F F' ≤ F.X := inf_le_left
  have hc3 : ∀ x ∈ F.X, (∀ w ∈ Formalism.HermitianLatticeCounting.S6.V0 F F', H.B w x = 0) ↔ x ∈ Formalism.HermitianLatticeCounting.S6.II F F' := by
    intro x hx
    constructor
    · intro hw
      have hxF' : x ∈ F'.X := by
        apply hA' x
        · intro a
          induction a using Fin.lastCases with
          | last => exact hw _ (lastVector_mem_jointSpan_right F F')
          | cast b => exact hw _ (isotropicSpan_le_jointSpan_right F F' ((e_mem_X F') b))
        · exact (X_iso F) hx hx
      exact Submodule.mem_inf.2 ⟨hx, hxF'⟩
    · intro hm w hw
      exact pairing_jointSpan_isotropicMeet F F' hm w hw
  refine ⟨fun v hv => ⟨fun hvw => ?_, fun hm w hw => B_swap0 H (pairing_jointSpan_isotropicMeet F F' hm w hw)⟩,
    ?_, hc3⟩
  · have hw' : ∀ w ∈ Formalism.HermitianLatticeCounting.S6.V0 F F', H.B w v = 0 := fun w hw => B_swap0 H (hvw w hw)
    rw [hJ] at hv
    obtain ⟨y, hy, t, ht, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.1 ht
    obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.1 hy
    rw [hI'] at hu'
    obtain ⟨s', hs', m, hm, rfl⟩ := Submodule.mem_sup.1 hu'
    have hD' : Formalism.HermitianLatticeCounting.S6.Dl F' F j (hj.trans (Nat.le_succ r)) ≠ 0 := by
      rw [Dl_swap]
      exact fun h0 => hD (star_eq_zero.1 h0)
    have hs'0 : s' = 0 := by
      apply Dl_injL F' F hj hD' hs'
      intro x hx
      have hxI : x ∈ F.X := (Xa_le_X F) j hx
      have h1 := hw' x (isotropicSpan_le_jointSpan_left F F' hxI)
      rw [HermSpace_B_add_right, HermSpace_B_add_right, HermSpace_B_add_right, HermSpace_B_smul_right_eq_star_mul, (X_iso F) hxI hu,
        (X_iso F) hxI (hmI hm), (pairing_isotropicSpan_lastVector F) hxI] at h1
      exact B_swap0 H (by simpa using h1)
    subst hs'0
    have hβ : β = 0 := by
      have h1 := hw' F.z (lastVector_mem_jointSpan_left F F')
      rw [zero_add, HermSpace_B_add_right, HermSpace_B_add_right, HermSpace_B_smul_right_eq_star_mul, (z_X F) hu,
        (z_X F) (hmI hm), (pairing_lastVector_lastVector F)] at h1
      have h2 : star β * F.T = 0 := by linear_combination -h1
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exact star_eq_zero.1 h3
      · exact absurd h3 F.hT
    subst hβ
    rw [zero_smul, add_zero, zero_add]
    rw [zero_smul, add_zero, zero_add] at hw'
    exact (hc3 _ (Submodule.add_mem _ hu (hmI hm))).1 hw'
  · have hII : F.X ⊔ F'.X = F.X ⊔ F'.Xa j := by
      apply le_antisymm
      · refine sup_le le_sup_left ?_
        rw [hI']
        exact sup_le le_sup_right (hmI.trans le_sup_left)
      · exact sup_le le_sup_left (le_sup_of_le_right ((Xa_le_X F') j))
    have hinf1 : F.X ⊓ F'.Xa j = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.1 hy
      have hmem : y ∈ Formalism.HermitianLatticeCounting.S6.II F F' ⊓ F'.Xa j :=
        Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hy1, (Xa_le_X F') j hy2⟩, hy2⟩
      rwa [hb'] at hmem
    have hfr1 : Module.finrank K ↥(F.X ⊔ F'.X) = r + j := by
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq F.X (F'.Xa j)
      rw [hinf1, finrank_bot, (finrank_X F), (finrank_Xa F') hj, ← hII] at h1
      omega
    have hinf2 : (F.X ⊔ F'.X) ⊓ (K ∙ F.z) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.1 hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy2
      by_cases ha : a = 0
      · rw [ha, zero_smul]
        exact Submodule.zero_mem _
      · exact absurd ((Submodule.smul_mem_iff _ ha).1 hy1) (lastVectorNotMemSup K V H r F F')
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq (F.X ⊔ F'.X) (K ∙ F.z)
    rw [hinf2, finrank_bot, hfr1, finrank_span_singleton (z_ne_zero F), ← hJ] at h2
    omega
end Formalism.HermitianLatticeCounting.P
