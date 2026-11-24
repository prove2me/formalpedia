-- Prove2me | solution 1 for Formalism.HN.hnStep_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:05.033547+00:00
-- url     : https://prove2.me/submissions/cd78f102-bdc4-4942-a68c-67484569d666

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNStep
import Theorems.Thm_Formalism_HN_imageLattice_mono
import Theorems.Thm_Formalism_F_saturProps


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
universe u v w
namespace Formalism.HN
theorem _root_.solution (h1 : DegSupermod.{u, v, w}) (h2 : MuChar.{u, v, w}) (h3 : RatioMax.{u, v, w})
    (h4 : FinSup.{u, v, w}) (h5 : SatR.{u, v, w}) (h6 : SatBasic.{u, v, w}) :
    HNStep.{u, v, w} := by
  intro R V E _ _ _ _ _ _ ρ L hL θ
  obtain ⟨hsub, hmono, hsat_eq, -, -, hbot, -, -⟩ := h6 R V E ρ L hL
  obtain ⟨g, hg⟩ : ∃ g : Submodule R V → ℝ, ∀ N, g N = deg ρ N - θ * (rk ρ N : ℝ) :=
    ⟨_, fun _ => rfl⟩
  have sm : ∀ A B : Submodule R V, A ≤ L → B ≤ L → g A + g B ≤ g (A ⊔ B) + g (A ⊓ B) := by
    intro A B hA hB
    obtain ⟨hr, hd⟩ := h1 R V E ρ L A B hL hA hB
    have hr' : (rk ρ (A ⊔ B) : ℝ) + rk ρ (A ⊓ B) = rk ρ A + rk ρ B := by
      exact_mod_cast hr
    have hθ : θ * (rk ρ (A ⊔ B) : ℝ) + θ * rk ρ (A ⊓ B) = θ * rk ρ A + θ * rk ρ B := by
      rw [← mul_add, ← mul_add, hr']
    simp only [hg]
    linarith
  have charP : ∀ M : Submodule R V, M ≤ L → M ≠ ⊥ →
      (θ ≤ muMin ρ M ↔ ∀ N ≤ M, g N ≤ g M) := by
    intro M hM hM0
    rw [(h2 R V E ρ M (hsub M hM) hM0).2.1 θ]
    refine forall_congr' fun N => imp_congr_right fun _ => ?_
    simp only [hg, mul_sub]
    constructor <;> intro h <;> linarith
  have supP : ∀ A B : Submodule R V, A ≤ L → B ≤ L → (∀ N ≤ A, g N ≤ g A) →
      (∀ N ≤ B, g N ≤ g B) → ∀ N ≤ A ⊔ B, g N ≤ g (A ⊔ B) := by
    intro A B hA hB pA pB N hN
    have hNL : N ≤ L := hN.trans (sup_le hA hB)
    have e1 := sm N A hNL hA
    have e2 := pA (N ⊓ A) inf_le_right
    have e3 := sm (N ⊔ A) B (sup_le hNL hA) hB
    have e4 := pB ((N ⊔ A) ⊓ B) inf_le_right
    have e5 : N ⊔ A ⊔ B = A ⊔ B := by
      rw [sup_assoc]; exact sup_eq_right.mpr hN
    rw [e5] at e3
    linarith
  obtain ⟨t, htS, htF⟩ := h4 R V E ρ L {N | N ≤ L ∧ N ≠ ⊥ ∧ θ ≤ muMin ρ N} hL
    (fun N hN => hN.1)
  have hFdef : hnStep ρ L θ = t.sup id := htF
  have memS : ∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → θ ≤ muMin ρ N →
      N ≤ hnStep ρ L θ := fun N a b c =>
    le_sSup (s := {N | N ≤ L ∧ N ≠ ⊥ ∧ θ ≤ muMin ρ N})
      (show N ≤ L ∧ N ≠ ⊥ ∧ θ ≤ muMin ρ N from ⟨a, b, c⟩)
  have PF : t.sup id ≤ L ∧ ∀ N ≤ t.sup id, g N ≤ g (t.sup id) := by
    refine Finset.sup_induction (p := fun M => M ≤ L ∧ ∀ N ≤ M, g N ≤ g M) ?_ ?_ ?_
    · refine ⟨bot_le, fun N hN => ?_⟩
      rw [le_bot_iff.mp hN]
    · rintro A ⟨hA, pA⟩ B ⟨hB, pB⟩
      exact ⟨sup_le hA hB, supP A B hA hB pA pB⟩
    · intro M hM
      have hM' : M ≤ L ∧ M ≠ ⊥ ∧ θ ≤ muMin ρ M := htS (Finset.mem_coe.mpr hM)
      exact ⟨hM'.1, (charP M hM'.1 hM'.2.1).mp hM'.2.2⟩
  rw [← hFdef] at PF
  obtain ⟨FL, PF⟩ := PF
  clear hFdef htF htS
  set F := hnStep ρ L θ with hFset
  clear_value F
  have rkpos_of : IsSat ρ L F → ∀ X : Submodule R V, F < X → X ≤ L →
      rk ρ F < rk ρ X := by
    intro hs X hX hXL
    rcases (hmono F X hX.le hXL).1.lt_or_eq with h | h
    · exact h
    · exact absurd (hsat_eq F X hs hX.le hXL h.symm) hX.ne'
  have Fsat : IsSat ρ L F := by
    obtain ⟨F', hFF', hF'L, himg⟩ := h5 R V E ρ L F hL FL
    obtain ⟨hsatimg, -, hrkimg⟩ := Formalism.F.saturProps E (zl ρ L)
      (zl ρ F) hL.2 (imageLattice_mono ρ FL)
    have hF'sat : IsSat ρ L F' := by
      unfold IsSat
      rw [himg]
      exact ⟨hF'L, hsatimg⟩
    have hrk : rk ρ F' = rk ρ F := by
      show Formalism.F.rk (zl ρ F') = Formalism.F.rk (zl ρ F)
      rw [himg]
      exact hrkimg
    by_cases hF'0 : F' = ⊥
    · have hF0 : F = ⊥ := by
        rw [eq_bot_iff, ← hF'0]
        exact hFF'
      rw [hF0]
      exact hbot
    · have PF' : ∀ N ≤ F', g N ≤ g F' := by
        intro M hM
        have hML : M ≤ L := hM.trans hF'L
        have e1 := sm M F hML FL
        have e2 := PF (M ⊓ F) inf_le_right
        have hX : M ⊔ F ≤ F' := sup_le hM hFF'
        have r1 := (hmono F (M ⊔ F) le_sup_right (hX.trans hF'L)).1
        have r2 := (hmono (M ⊔ F) F' hX hF'L).1
        have hreq : rk ρ (M ⊔ F) = rk ρ F' := by omega
        have d := (hmono (M ⊔ F) F' hX hF'L).2 hreq
        have e3 : g (M ⊔ F) ≤ g F' := by
          simp only [hg, hreq]
          linarith
        linarith
      have hmem := memS F' hF'L hF'0 ((charP F' hF'L hF'0).mpr PF')
      rw [le_antisymm hmem hFF'] at hF'sat
      exact hF'sat
  refine ⟨Fsat, fun hF0 => (charP F FL hF0).mpr PF, memS, ?_⟩
  intro N hFN hNL
  refine not_le.mp fun hcon => ?_
  have rkpos := rkpos_of Fsat
  have hFL : F ≠ L := (lt_of_lt_of_le hFN hNL).ne
  obtain ⟨N₀, hFN₀, hN₀sat, hmax⟩ := h3 R V E ρ L F hL Fsat hFL
  have hN₀L : N₀ ≤ L := by
    unfold IsSat at hN₀sat
    exact hN₀sat.1
  have hr₀ : (rk ρ F : ℝ) < rk ρ N₀ := by exact_mod_cast rkpos N₀ hFN₀ hN₀L
  have hr : (rk ρ F : ℝ) < rk ρ N := by exact_mod_cast rkpos N hFN hNL
  have key := hmax N hFN hNL
  have hμ : θ * ((rk ρ N₀ : ℝ) - rk ρ F) ≤ deg ρ N₀ - deg ρ F := by
    refine not_lt.mp fun hlt => ?_
    have a1 := mul_lt_mul_of_pos_right hlt (sub_pos.mpr hr)
    have a2 := mul_le_mul_of_nonneg_right hcon (sub_pos.mpr hr₀).le
    nlinarith
  have PN₀ : ∀ M ≤ N₀, g M ≤ g N₀ := by
    intro M hM
    have hML : M ≤ L := hM.trans hN₀L
    have e1 := sm M F hML FL
    have e2 := PF (M ⊓ F) inf_le_right
    have hX : M ⊔ F ≤ N₀ := sup_le hM hFN₀.le
    have hXN₀ : g (M ⊔ F) ≤ g N₀ := by
      rcases (le_sup_right : F ≤ M ⊔ F).lt_or_eq with hlt | heq
      · have hrX₀ : (rk ρ (M ⊔ F) : ℝ) ≤ rk ρ N₀ := by
          exact_mod_cast (hmono _ _ hX hN₀L).1
        have k2 := hmax (M ⊔ F) hlt (hX.trans hN₀L)
        have hpos : 0 < (rk ρ N₀ : ℝ) - rk ρ F := sub_pos.mpr hr₀
        have hm : ((rk ρ N₀ : ℝ) - rk ρ F) * g (M ⊔ F) ≤
            ((rk ρ N₀ : ℝ) - rk ρ F) * g N₀ := by
          simp only [hg]
          nlinarith [mul_nonneg (sub_nonneg.mpr hμ) (sub_nonneg.mpr hrX₀)]
        exact le_of_mul_le_mul_left hm hpos
      · rw [← heq]
        simp only [hg]
        linarith [mul_sub θ (rk ρ N₀ : ℝ) (rk ρ F)]
    linarith
  have hN₀0 : N₀ ≠ ⊥ := ne_bot_of_gt hFN₀
  have hle := memS N₀ hN₀L hN₀0 ((charP N₀ hN₀L hN₀0).mpr PN₀)
  exact absurd (le_antisymm hle hFN₀.le) hFN₀.ne'
end Formalism.HN
