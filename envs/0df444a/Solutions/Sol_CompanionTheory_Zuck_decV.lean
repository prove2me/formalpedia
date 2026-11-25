-- Prove2me | solution 1 for CompanionTheory.Zuck.decV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:04:37.365107+00:00
-- url     : https://prove2.me/submissions/04f20c89-0720-44d6-84c6-2baa864b6f43

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_MultOne
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_ShiftApply
import Theorems.Thm_CompanionTheory_Zuck_shift_shift
import Theorems.Thm_CompanionTheory_Zuck_gap_shift
import Theorems.Thm_CompanionTheory_Zuck_cas_ne
import Theorems.Thm_CompanionTheory_Zuck_shift_inj
import Theorems.Thm_CompanionTheory_Zuck_iso_of
import Theorems.Thm_CompanionTheory_Zuck_injV
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply



set_option autoImplicit false
open Matrix Finset
open scoped Kronecker
noncomputable section
open CompanionTheory CompanionTheory.Zuck
open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData
open PI.UpqRep (IsHCParam)
open PI.ZuckTensor (GapAtLeast)
variable {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
namespace CompanionTheory.Zuck
theorem _root_.solution (S : Steps) (Lb : Lib t) (hk : 1 ≤ k) (b : Bool) {μ : Fin (2 * r + k + 1) → ℝ} {U : URep k r} {h : ℝ}
    (hU : U.R.IsDS ε μ) (hg : GapAtLeast ε μ h) (ht : t _ ε + (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) + 1 < h)
    (T : Fin (2 * r + k + 1) → URep k r) (hT : ∀ s, (T s).R.IsDS ε (shift b μ s)) :
    ∃ io pr, IsDec (N := M) IsHom (vr k r b, U) (fun s => one (T s)) io pr := by
  have C := S.homCat k r
  have h1 : (1 : ℝ) ≤ (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hsimp := S.schur S.infChar k r ε _ _ T (shift_inj b μ) hT
  have adj' : ∀ U U' : URep k r, ∃ e : (M (vr k r (!b), U) →ₗ[ℂ] M (one U')) ≃ₗ[ℂ] (M (one U) →ₗ[ℂ] M (vr k r b, U')),
      ∀ p, IsHom (vr k r (!b), U) (one U') p ↔ IsHom (one U) (vr k r b, U') (e p) := by
    cases b
    · exact S.adj k r true
    · exact S.adj k r false
  have occ : ∀ s, ∃ i, IsHom (one (T s)) (vr k r b, U) i ∧ i ≠ 0 := by
    intro s
    obtain ⟨T', hT', -, hp⟩ := injV S Lb (!b) (hT s) (gap_shift hg b s) (by linarith)
    have hs : IsHCParam (shift (!b) (shift b μ s) s) := by rw [shift_shift]; exact hU.1
    obtain ⟨p, hp, hp0⟩ := hp ⟨s, hs⟩
    have hd : (T' ⟨s, hs⟩).R.IsDS ε μ := by simpa only [shift_shift] using hT' ⟨s, hs⟩
    obtain ⟨f, g, hf, -, hgf, -⟩ := iso_of S Lb hd hU hg (by linarith)
    obtain ⟨e, he⟩ := adj' (T s) U
    refine ⟨e (f ∘ₗ p), (he _).1 (C.comp _ _ _ _ _ hp hf), fun h0 => hp0 ?_⟩
    have h2 : f ∘ₗ p = 0 := e.map_eq_zero_iff.1 h0
    calc p = (g ∘ₗ f) ∘ₗ p := by rw [hgf, LinearMap.id_comp]
      _ = 0 := by rw [LinearMap.comp_assoc, h2, LinearMap.comp_zero]
  refine S.decOfInj _ _ _ C _ _ _ hsimp ?_ (fun s => ?_) occ
  · obtain ⟨T', hT', hi, -⟩ := injV S Lb b hU hg (by linarith)
    intro x hx
    refine hi x fun s p hp => ?_
    obtain ⟨f, g, hf, -, hgf, -⟩ := iso_of S Lb (hT' s) (hT s.1) (gap_shift hg b s.1) (by linarith)
    have h2 := hx s.1 _ (C.comp _ _ _ _ _ hp hf)
    have h3 := LinearMap.congr_fun hgf (p x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2 h3
    rw [← h3, h2, map_zero]
  · obtain ⟨T', hT', hi, -⟩ := injV S Lb b (hT s) (gap_shift hg b s) (by linarith)
    have cB := S.casDS S.infChar k r ε _ (T s) hk (hT s)
    have m1 : AtMostOne (N := M) IsHom (one U) (vr k r (!b), T s) := by
      have := fun hi' ho' => S.multOne k r (!b) (T s) U _ T' _ _ _ (fun F => (cB F).1) (cB (triv k r)).2
        (S.casDS S.infChar k r ε _ U hk hU (triv k r)).2
        (fun u => (S.casDS S.infChar k r ε _ (T' u) hk (hT' u) (triv k r)).2)
        (fun u => cas_ne hU.1.1 b s u.1) hi' (hsimp.2.1 s) ⟨_, _, hU⟩ ho'
      cases b
      · exact this hi (occ s)
      · exact this hi (occ s)
    obtain ⟨e, he⟩ := S.adj k r b U (T s)
    intro f g hf hg'
    obtain ⟨α, β, hab, h0⟩ := m1 _ _ ((he f).1 hf) ((he g).1 hg')
    refine ⟨α, β, hab, e.map_eq_zero_iff.1 ?_⟩
    rw [map_add, map_smul, map_smul, h0]
end CompanionTheory.Zuck
