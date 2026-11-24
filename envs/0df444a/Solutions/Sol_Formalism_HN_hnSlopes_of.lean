-- Prove2me | solution 1 for Formalism.HN.hnSlopes_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:14.621513+00:00
-- url     : https://prove2.me/submissions/f08b60ff-11b3-4b49-8bd7-dc604ea0faad

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FinSup
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNStep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Theorems.Thm_Formalism_HN_card_filter_val_lt_alt
import Theorems.Thm_Formalism_HN_sum_ite_val_lt_sub_mul_mono
import Theorems.Thm_Formalism_HN_sum_ite_val_lt_sub_mul_anti
import Theorems.Thm_Formalism_HN_eq_zero_of_abs_le_mul

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
theorem _root_.solution (h1 : HNStep.{u, v, w}) (h2 : MuChar.{u, v, w})
    (h3 : DegSupermod.{u, v, w}) (h4 : SatBasic.{u, v, w}) : HNSlopes.{u, v, w} := by
  intro R V E _ _ _ _ _ _ ρ L hL
  obtain ⟨hSubLat, hMono, hSatEq, hRk0, hDeg0, -, -, -⟩ := h4 R V E ρ L hL
  have hstep := h1 R V E ρ L hL
  have hHL : ∀ θ, hnStep ρ L θ ≤ L := fun θ => by
    unfold hnStep
    exact sSup_le fun N hN => hN.1
  have hHanti : ∀ θ θ' : ℝ, θ ≤ θ' → hnStep ρ L θ' ≤ hnStep ρ L θ := fun θ θ' h => by
    unfold hnStep
    exact sSup_le_sSup fun N hN => ⟨hN.1, hN.2.1, le_trans h hN.2.2⟩
  have hr_anti : ∀ θ θ' : ℝ, θ ≤ θ' → rk ρ (hnStep ρ L θ') ≤ rk ρ (hnStep ρ L θ) :=
    fun θ θ' h => (hMono _ _ (hHanti θ θ' h) (hHL θ)).1
  have hr_le : ∀ θ, rk ρ (hnStep ρ L θ) ≤ rk ρ L := fun θ => (hMono _ _ (hHL θ) le_rfl).1
  have hrk_bot : rk ρ (⊥ : Submodule R V) = 0 := (hRk0 ⊥ bot_le).mpr rfl
  have hne_of : ∀ θ, 0 < rk ρ (hnStep ρ L θ) → hnStep ρ L θ ≠ ⊥ := fun θ h he => by
    rw [he, hrk_bot] at h
    exact lt_irrefl 0 h
  have hLne_of : ∀ θ, hnStep ρ L θ ≠ ⊥ → L ≠ ⊥ := fun θ h hL0 =>
    h (le_bot_iff.mp (le_trans (hHL θ) (le_of_eq hL0)))

  have hbdd : ∀ j : ℕ, BddAbove {θ : ℝ | j < rk ρ (hnStep ρ L θ)} := by
    intro j
    refine ⟨muMax ρ L, fun θ hθ => ?_⟩
    have hθ' : j < rk ρ (hnStep ρ L θ) := hθ
    have hne : hnStep ρ L θ ≠ ⊥ := hne_of θ (lt_of_le_of_lt (Nat.zero_le j) hθ')
    have hLne := hLne_of θ hne
    have hMH := h2 R V E ρ (hnStep ρ L θ) (hSubLat _ (hHL θ)) hne
    have hML := h2 R V E ρ L hL hLne
    have hmax : muMax ρ (hnStep ρ L θ) ≤ muMax ρ L :=
      (hMH.1 (muMax ρ L)).mpr fun N hN =>
        (hML.1 (muMax ρ L)).mp le_rfl N (le_trans hN (hHL θ))
    exact le_trans ((hstep θ).2.1 hne) (le_trans hMH.2.2.2.1 (le_trans hMH.2.2.2.2 hmax))

  have hatt : ∀ j : ℕ, j < rk ρ L →
      j < rk ρ (hnStep ρ L (sSup {θ : ℝ | j < rk ρ (hnStep ρ L θ)})) := by
    intro j hj
    have hLne : L ≠ ⊥ := fun h0 => by
      rw [h0, hrk_bot] at hj
      exact Nat.not_lt_zero _ hj
    have hSne : ({θ : ℝ | j < rk ρ (hnStep ρ L θ)}).Nonempty := by
      refine ⟨muMin ρ L, ?_⟩
      have hLH : L ≤ hnStep ρ L (muMin ρ L) := (hstep _).2.2.1 L le_rfl hLne le_rfl
      exact lt_of_lt_of_le hj (hMono _ _ hLH (hHL _)).1
    have hbelow : ∀ θ, θ < sSup {θ : ℝ | j < rk ρ (hnStep ρ L θ)} →
        j < rk ρ (hnStep ρ L θ) := by
      intro θ hθ
      obtain ⟨θ₂, hθ₂, hlt⟩ := exists_lt_of_lt_csSup hSne hθ
      exact lt_of_lt_of_le hθ₂ (hr_anti θ θ₂ hlt.le)
    obtain ⟨s, hs⟩ : ∃ s, s = sSup {θ : ℝ | j < rk ρ (hnStep ρ L θ)} := ⟨_, rfl⟩
    rw [← hs] at hbelow ⊢
    have hex : ∃ c : ℕ, ∃ θ : ℝ, θ < s ∧ rk ρ (hnStep ρ L θ) = c :=
      ⟨_, s - 1, by linarith, rfl⟩
    classical
    obtain ⟨θ₀, hθ₀s, hθ₀c⟩ := Nat.find_spec hex
    have hconst : ∀ θ, θ₀ ≤ θ → θ < s → hnStep ρ L θ₀ = hnStep ρ L θ := by
      intro θ h0 hθs
      have hle : rk ρ (hnStep ρ L θ) ≤ rk ρ (hnStep ρ L θ₀) := hr_anti θ₀ θ h0
      have hge : Nat.find hex ≤ rk ρ (hnStep ρ L θ) := Nat.find_min' hex ⟨θ, hθs, rfl⟩
      exact hSatEq _ _ (hstep θ).1 (hHanti θ₀ θ h0) (hHL θ₀) (by omega)
    have hne0 : hnStep ρ L θ₀ ≠ ⊥ :=
      hne_of θ₀ (lt_of_le_of_lt (Nat.zero_le j) (hbelow θ₀ hθ₀s))
    have hμ : s ≤ muMin ρ (hnStep ρ L θ₀) := by
      by_contra hlt
      push_neg at hlt
      obtain ⟨θ, hθdef⟩ : ∃ θ, θ = max θ₀ ((muMin ρ (hnStep ρ L θ₀) + s) / 2) := ⟨_, rfl⟩
      have h1' : θ₀ ≤ θ := by rw [hθdef]; exact le_max_left _ _
      have h2' : θ < s := by rw [hθdef]; exact max_lt hθ₀s (by linarith)
      have h4' : (muMin ρ (hnStep ρ L θ₀) + s) / 2 ≤ θ := by rw [hθdef]; exact le_max_right _ _
      have heq := hconst θ h1' h2'
      have hneθ : hnStep ρ L θ ≠ ⊥ := heq ▸ hne0
      have h3' := (hstep θ).2.1 hneθ
      rw [← heq] at h3'
      linarith
    have hsub : hnStep ρ L θ₀ ≤ hnStep ρ L s := (hstep s).2.2.1 _ (hHL θ₀) hne0 hμ
    exact lt_of_lt_of_le (hbelow θ₀ hθ₀s) (hMono _ _ hsub (hHL s)).1
  have hiff : ∀ j : Fin (rk ρ L), ∀ θ : ℝ,
      ((j : ℕ) < rk ρ (hnStep ρ L θ) ↔ θ ≤ slopeList ρ L j) := by
    intro j θ
    constructor
    · intro h
      exact le_csSup (hbdd j) h
    · intro h
      exact lt_of_lt_of_le (hatt j j.2)
        (hr_anti θ (sSup {θ : ℝ | (j : ℕ) < rk ρ (hnStep ρ L θ)}) h)
  have hanti : Antitone (slopeList ρ L) := by
    intro i j hij
    exact (hiff i _).mp (lt_of_le_of_lt (show (i : ℕ) ≤ j from hij) ((hiff j _).mpr le_rfl))
  have hP : ∀ k, hnPoly ρ L k =
      ∑ j : Fin (rk ρ L), if (j : ℕ) < k then slopeList ρ L j else 0 := fun k => rfl

  have hpoly : ∀ θ, deg ρ (hnStep ρ L θ) = hnPoly ρ L (rk ρ (hnStep ρ L θ)) := by
    suffices H : ∀ c : ℕ, ∀ θ, rk ρ (hnStep ρ L θ) = c →
        deg ρ (hnStep ρ L θ) = hnPoly ρ L c from fun θ => H _ θ rfl
    intro c
    induction c using Nat.strong_induction_on with
    | _ c ih =>
      intro θ hθc
      rcases Nat.eq_zero_or_pos c with hc0 | hcpos
      · have hb : hnStep ρ L θ = ⊥ := (hRk0 _ (hHL θ)).mp (hθc.trans hc0)
        rw [hb, hDeg0, hc0, hP]
        simp
      · have hcn : c ≤ rk ρ L := hθc ▸ hr_le θ
        let jj : Fin (rk ρ L) := ⟨c - 1, by omega⟩
        have hθt : θ ≤ slopeList ρ L jj :=
          (hiff jj θ).mp (by show c - 1 < rk ρ (hnStep ρ L θ); omega)
        have htj : c - 1 < rk ρ (hnStep ρ L (slopeList ρ L jj)) := (hiff jj _).mpr le_rfl
        have hrt : rk ρ (hnStep ρ L (slopeList ρ L jj)) = c := by
          have := hr_anti _ _ hθt
          omega
        have hHt : hnStep ρ L θ = hnStep ρ L (slopeList ρ L jj) :=
          hSatEq _ _ (hstep _).1 (hHanti _ _ hθt) (hHL θ) (by omega)
        have hneθ : hnStep ρ L θ ≠ ⊥ := hne_of θ (by omega)
        have hMC := h2 R V E ρ (hnStep ρ L θ) (hSubLat _ (hHL θ)) hneθ
        have htmu : slopeList ρ L jj ≤ muMin ρ (hnStep ρ L θ) := by
          rw [hHt]
          exact (hstep _).2.1 (hHt ▸ hneθ)
        have hz : deg ρ (hnStep ρ L θ) - hnPoly ρ L c = 0 := by
          apply eq_zero_of_abs_le_mul _ (rk ρ L)
          intro ε hε
          obtain ⟨t, ht⟩ : ∃ t, t = slopeList ρ L jj := ⟨_, rfl⟩
          rw [← ht] at hHt htmu hrt
          have hc' : rk ρ (hnStep ρ L (t + ε)) < c := by
            have : ¬ (c - 1 < rk ρ (hnStep ρ L (t + ε))) := fun h => by
              have h' := (hiff jj _).mp h
              rw [← ht] at h'
              linarith
            omega
          have ih' := ih _ hc' (t + ε) rfl
          have hle' : hnStep ρ L (t + ε) ≤ hnStep ρ L θ :=
            (hHanti t (t + ε) (by linarith)).trans hHt.ge
          have hlt' : hnStep ρ L (t + ε) < hnStep ρ L θ := lt_of_le_of_ne hle' (fun h => by
            rw [h] at hc'
            omega)
          have hD := (hstep (t + ε)).2.2.2 _ hlt' (hHL θ)
          have hD2 := (hMC.2.1 t).mp htmu _ hle'
          have hP1 : hnPoly ρ L (rk ρ (hnStep ρ L (t + ε))) - t * (rk ρ (hnStep ρ L (t + ε)) : ℕ)
              ≤ hnPoly ρ L c - t * (c : ℕ) :=
            sum_ite_val_lt_sub_mul_mono (rk ρ L) _ c hc'.le hcn (slopeList ρ L) t
              (fun j _ h2 => (hiff j t).mp (by omega))
          have hP2 : hnPoly ρ L c - (t + ε) * (c : ℕ) ≤
              hnPoly ρ L (rk ρ (hnStep ρ L (t + ε))) - (t + ε) * (rk ρ (hnStep ρ L (t + ε)) : ℕ) :=
            sum_ite_val_lt_sub_mul_anti (rk ρ L) _ c hc'.le hcn (slopeList ρ L) (t + ε)
              (fun j h1 _ => le_of_lt (not_le.mp fun h => by
                have := (hiff j _).mpr h
                omega))
          rw [hθc] at hD hD2
          have hcL : (c : ℝ) ≤ rk ρ L := by exact_mod_cast hcn
          have hr0 : (0 : ℝ) ≤ (rk ρ (hnStep ρ L (t + ε)) : ℝ) := Nat.cast_nonneg _
          have hεΔ : ε * ((c : ℝ) - rk ρ (hnStep ρ L (t + ε))) ≤ ε * rk ρ L :=
            mul_le_mul_of_nonneg_left (by linarith) hε.le
          have e1 : (t + ε) * ((c : ℝ) - rk ρ (hnStep ρ L (t + ε))) =
              t * c - t * rk ρ (hnStep ρ L (t + ε)) + ε * c - ε * rk ρ (hnStep ρ L (t + ε)) := by
            ring
          have e2 : t * ((c : ℝ) - rk ρ (hnStep ρ L (t + ε))) =
              t * c - t * rk ρ (hnStep ρ L (t + ε)) := by ring
          have e3 : (t + ε) * (c : ℝ) = t * c + ε * c := by ring
          have e4 : (t + ε) * (rk ρ (hnStep ρ L (t + ε)) : ℝ) =
              t * rk ρ (hnStep ρ L (t + ε)) + ε * rk ρ (hnStep ρ L (t + ε)) := by ring
          have e5 : ε * ((c : ℝ) - rk ρ (hnStep ρ L (t + ε))) =
              ε * c - ε * rk ρ (hnStep ρ L (t + ε)) := by ring
          rw [abs_le]
          constructor <;> linarith
        exact sub_eq_zero.mp hz
  have hfull : ∃ θ, hnStep ρ L θ = L := by
    by_cases hL0 : L = ⊥
    · refine ⟨0, le_antisymm (hHL 0) ?_⟩
      rw [hL0]
      exact bot_le
    · exact ⟨muMin ρ L, le_antisymm (hHL _) ((hstep _).2.2.1 L le_rfl hL0 le_rfl)⟩
  have hsum : ∑ j, slopeList ρ L j = deg ρ L := by
    obtain ⟨θ, hθ⟩ := hfull
    have h := hpoly θ
    rw [hθ] at h
    rw [h, hP]
    exact Finset.sum_congr rfl fun j _ => (if_pos j.2).symm

  have hsubmax : ∀ θ (M : Submodule R V), M ≤ hnStep ρ L θ →
      deg ρ M - θ * rk ρ M ≤ deg ρ (hnStep ρ L θ) - θ * rk ρ (hnStep ρ L θ) := by
    intro θ M hM
    by_cases hH : hnStep ρ L θ = ⊥
    · have hM0 : M = ⊥ := le_bot_iff.mp (hM.trans hH.le)
      simp only [hM0, hH, le_refl]
    · have hMC := h2 R V E ρ _ (hSubLat _ (hHL θ)) hH
      have := (hMC.2.1 θ).mp ((hstep θ).2.1 hH) M hM
      rw [mul_sub] at this
      linarith
  have hmax : ∀ θ (N : Submodule R V), N ≤ L →
      deg ρ N - θ * rk ρ N ≤ deg ρ (hnStep ρ L θ) - θ * rk ρ (hnStep ρ L θ) := by
    intro θ N hN
    obtain ⟨hrk, hdeg⟩ := h3 R V E ρ L N (hnStep ρ L θ) hL hN (hHL θ)
    have hrk' : ((rk ρ (N ⊔ hnStep ρ L θ) : ℕ) : ℝ) + rk ρ (N ⊓ hnStep ρ L θ) =
        rk ρ N + rk ρ (hnStep ρ L θ) := by exact_mod_cast hrk
    have hinf := hsubmax θ _ (inf_le_right : N ⊓ hnStep ρ L θ ≤ _)
    have hsup : deg ρ (N ⊔ hnStep ρ L θ) - θ * rk ρ (N ⊔ hnStep ρ L θ) ≤
        deg ρ (hnStep ρ L θ) - θ * rk ρ (hnStep ρ L θ) := by
      by_cases heq : N ⊔ hnStep ρ L θ = hnStep ρ L θ
      · simp only [heq, le_refl]
      · have := (hstep θ).2.2.2 _ (lt_of_le_of_ne le_sup_right (Ne.symm heq))
          (sup_le hN (hHL θ))
        rw [mul_sub] at this
        linarith
    have e : θ * (rk ρ (N ⊔ hnStep ρ L θ) : ℝ) + θ * rk ρ (N ⊓ hnStep ρ L θ) =
        θ * rk ρ N + θ * rk ρ (hnStep ρ L θ) := by rw [← mul_add, ← mul_add, hrk']
    linarith
  have hpolyle : ∀ N : Submodule R V, N ≤ L → deg ρ N ≤ hnPoly ρ L (rk ρ N) := by
    intro N hN
    rcases Nat.eq_zero_or_pos (rk ρ N) with hk0 | hkpos
    · have hN0 : N = ⊥ := (hRk0 N hN).mp hk0
      rw [hk0, hN0, hDeg0, hP]
      simp
    · have hkn : rk ρ N ≤ rk ρ L := (hMono _ _ hN le_rfl).1
      let jj : Fin (rk ρ L) := ⟨rk ρ N - 1, by omega⟩
      have hr : rk ρ N - 1 < rk ρ (hnStep ρ L (slopeList ρ L jj)) := (hiff jj _).mpr le_rfl
      have hm := hmax (slopeList ρ L jj) N hN
      rw [hpoly] at hm
      have hA : hnPoly ρ L (rk ρ (hnStep ρ L (slopeList ρ L jj))) -
          slopeList ρ L jj * (rk ρ (hnStep ρ L (slopeList ρ L jj)) : ℕ) ≤
          hnPoly ρ L (rk ρ N) - slopeList ρ L jj * (rk ρ N : ℕ) :=
        sum_ite_val_lt_sub_mul_anti _ _ _ (by omega) (hr_le _) (slopeList ρ L) _
          (fun j h1 _ => hanti (show jj ≤ j from (show rk ρ N - 1 ≤ (j : ℕ) by omega)))
      linarith
  refine ⟨hanti, ?_, hsum, hpolyle, hpoly⟩
  intro θ
  convert card_filter_val_lt_alt _ _ (hr_le θ) using 2
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (hiff j θ).symm
end Formalism.HN
