-- Prove2me | solution 1 for BunkbedAux.phiExt_involution
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T01:55:12.444968+00:00
-- url     : https://prove2.me/submissions/2daa3303-0305-41b5-bfa9-d44953d2aadb

import Definitions.Def_BunkbedWZSurgery

open Bunkbed Bunkbed.Hyper Finset SimpleGraph

lemma legal_rho : ∀ q : WZExt, WZExt.legal q = true → WZExt.legal (WZExt.rho q) = true := by
  decide
lemma lam_legal : ∀ q : WZExt, WZExt.inLamSq q = true → WZExt.legal q = true := by decide
lemma eta_inv : ∀ q : WZExt, WZExt.inLamSq q = true → WZExt.eta (WZExt.eta q) = q := by decide
lemma eta_lam : ∀ q : WZExt, WZExt.inLamSq q = true → WZExt.inLamSq (WZExt.eta q) = true := by
  decide
lemma rho_inv : ∀ q : WZExt, WZExt.rho (WZExt.rho q) = q := by decide
lemma wt_rho (P : WZ → ℚ) : ∀ q : WZExt, WZExt.wt P (WZExt.rho q) = WZExt.wt P q := by
  intro q
  rcases q with ⟨a, b⟩ | i
  · cases a <;> cases b <;> simp only [WZExt.wt, WZExt.rho] <;> ring
  · fin_cases i <;> simp only [WZExt.wt, WZExt.rho] <;> ring
lemma wt_eta (P : WZ → ℚ) : ∀ q : WZExt, WZExt.inLamSq q = true →
    WZExt.wt P (WZExt.eta q) = WZExt.wt P q := by
  intro q hq
  rcases q with ⟨a, b⟩ | i
  · cases a <;> cases b <;> simp_all [WZExt.wt, WZExt.eta, WZExt.inLamSq] <;> ring
  · fin_cases i <;> simp_all [WZExt.wt, WZExt.eta, WZExt.inLamSq] <;> ring

/-- **`phiExt e` is a weight-preserving involution fixing the pivot.** -/
theorem solution (P : WZ → ℚ) (e : Fin 6) (Ψ : Fin 6 → WZExt)
    (hleg : ∀ h, WZExt.legal (Ψ h) = true)
    (he : WZExt.inLamSq (Ψ e) = true)
    (hmin : ∀ h : Fin 6, h.val < e.val → WZExt.inLamSq (Ψ h) = false) :
    (∀ h, WZExt.legal (phiExt e Ψ h) = true)
    ∧ WZExt.inLamSq (phiExt e Ψ e) = true
    ∧ (∀ h : Fin 6, h.val < e.val → WZExt.inLamSq (phiExt e Ψ h) = false)
    ∧ phiExt e (phiExt e Ψ) = Ψ
    ∧ (∏ h, WZExt.wt P (phiExt e Ψ h)) = ∏ h, WZExt.wt P (Ψ h) := by
  have hpe : phiExt e Ψ e = WZExt.eta (Ψ e) := by simp [phiExt]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    by_cases h1 : h.val < e.val
    · simpa [phiExt, h1] using hleg h
    · by_cases h2 : h = e
      · rw [h2, hpe]; exact lam_legal _ (eta_lam _ he)
      · simpa [phiExt, h1, h2] using legal_rho _ (hleg h)
  · rw [hpe]; exact eta_lam _ he
  · intro h h1; simpa [phiExt, h1] using hmin h h1
  · funext h
    by_cases h1 : h.val < e.val
    · simp [phiExt, h1]
    · by_cases h2 : h = e
      · rw [h2]
        have hlt : ¬ (e.val < e.val) := lt_irrefl _
        simp only [phiExt, hlt, if_false, if_pos rfl]
        exact eta_inv _ he
      · have h3 : ¬ (h.val < e.val) := h1
        simp only [phiExt, h3, if_false, if_neg h2]
        exact rho_inv _
  · refine Finset.prod_congr rfl (fun h _ => ?_)
    by_cases h1 : h.val < e.val
    · simp [phiExt, h1]
    · by_cases h2 : h = e
      · rw [h2, hpe]; exact wt_eta P _ he
      · simp only [phiExt, h1, if_false, if_neg h2]
        exact wt_rho P _
