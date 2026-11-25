-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.wt_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:41:37.174085+00:00
-- url     : https://prove2.me/submissions/dae8b702-eb79-44ca-93aa-00d01b4b3f8c

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_ChainI
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseKOneHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_rho_le_top
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_v_al_two
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_lR
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_l_ne
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_q_cast
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_q_rho
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_wt_m
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_wt_m_pow_sub_frob
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_wt_m_rho
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_C_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_add
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_mono
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_pow
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_C_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mono
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow
import Theorems.Thm_Formalism_BaseCaseIdentities_hasWt_add_pow_sub
import Theorems.Thm_Formalism_BaseCaseIdentities_identity_twenty_d
import Theorems.Thm_Formalism_BaseCaseIdentities_num_good
import Theorems.Thm_Formalism_BaseCaseIdentities_rho_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_rho_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
open Formalism.BaseCaseIdentities.Data
variable {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C] (D : Data k Z C)
namespace Formalism.BaseCaseIdentities.Data
theorem _root_.solution (J : ℕ) (hJK : J ≤ D.K) (c b : C) (hcJ : D.lev c < J) (τ : MvPowerSeries Z k)
    (hν : D.Wt D.top (τ - D.m (D.lev c) c)) :
    D.Wt D.top (MvPowerSeries.C (D.al c 2 b) * τ ^ (D.l ^ 2) + D.main J c b) := by
  have hl := D.l_ge
  have hcK : D.lev c < D.K := by omega
  have hgood := D.pure_good c hcK
  have hal := D.v_al_two c hgood b
  have hρ := rho_pos hl
  obtain ⟨μ, hμdef⟩ : ∃ μ, μ = D.m (D.lev c) c := ⟨_, rfl⟩
  obtain ⟨ν, hνdef⟩ : ∃ ν, ν = τ - μ := ⟨_, rfl⟩
  have hτ : τ = μ + ν := by rw [hνdef]; ring
  have hμ : D.Wt (rho D.l) μ := by rw [hμdef]; exact D.wt_m_rho _ _
  have hν' : D.Wt D.top ν := by rw [hνdef, hμdef]; exact hν
  have hdec : MvPowerSeries.C (D.al c 2 b) * τ ^ (D.l ^ 2) + D.main J c b =
      MvPowerSeries.C (D.al c 2 b) * (μ ^ (D.l ^ 2) - frob D.q μ)
      + MvPowerSeries.C (D.al c 2 b) * ((μ + ν) ^ (D.l ^ 2) - μ ^ (D.l ^ 2) - ν ^ (D.l ^ 2))
      + MvPowerSeries.C (D.al c 2 b) * ν ^ (D.l ^ 2)
      + (MvPowerSeries.C (D.al c 2 b) * frob D.q μ + D.main J c b) := by
    rw [hτ]; ring
  rw [hdec]
  have hqρ := D.q_rho
  refine HasWt.add (HasWt.add (HasWt.add ?_ ?_) ?_) ?_
  · have h1 : D.Wt (1 + qnum D.l * rho D.l) (μ ^ (D.l ^ 2) - frob D.q μ) := by
      rw [hμdef]; exact D.wt_m_pow_sub_frob hcK c
    refine HasWt.mono ?_ (HasWt.C_mul hal h1)
    unfold top
    linarith
  · have h1 := hasWt_add_pow_sub (e := 2) D.l_prime D.v_l D.rho_le_top hμ hν'
    refine HasWt.mono ?_ (HasWt.C_mul hal h1)
    have := rho_mul hl
    push_cast
    linarith
  · have h1 := HasWt.pow hν' (D.l ^ 2)
    refine HasWt.mono ?_ (HasWt.C_mul hal h1)
    have := num_good hl (j := 2) le_rfl
    unfold top
    push_cast at this ⊢
    linarith
  · by_cases hK1 : D.lev c + 1 < D.K
    · rw [main, if_pos ⟨hcJ, hK1⟩, ← hμdef, ← add_mul, ← map_add]
      have h1 : D.al c 2 b + -(D.l : k)⁻¹ * D.g c b = D.lam c b := by
        rw [D.al_two c hcK b]
        have := D.l_ne
        field_simp
        ring
      rw [h1]
      have h2 : ((0 : ℝ) : WithTop ℝ) ≤ D.v (D.lam c b) := by simpa using D.lam_int c b
      refine HasWt.mono ?_ (HasWt.C_mul h2 (HasWt.frob hμ D.q))
      rw [D.q_cast]
      unfold top
      linarith
    · rw [main, if_neg (fun h => hK1 h.2), add_zero]
      have h1 : D.Wt (rho D.l + qnum D.l ^ (D.lev c) * sg D.l D.i) μ := by
        rw [hμdef]; exact D.wt_m _ _
      refine HasWt.mono ?_ (HasWt.C_mul hal (HasWt.frob h1 D.q))
      rw [D.q_cast]
      have hlev : D.lev c + 1 = Kn D.i := by
        have : D.K = Kn D.i := rfl
        omega
      have h2 := identity_twenty_d D.l D.i (by omega) D.i_odd
      rw [← hlev, pow_succ'] at h2
      have := D.lR
      unfold top
      nlinarith
end Formalism.BaseCaseIdentities.Data
