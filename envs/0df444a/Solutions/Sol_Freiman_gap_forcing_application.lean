-- Prove2me | solution 1 for Freiman.gap_forcing_application
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:21:34.149742+00:00
-- url     : https://prove2.me/submissions/c8720a86-0d1a-4f1c-8e7a-f84b25214f1b

import Theorems.Thm_Freiman_gap_capped_digits
import Theorems.Thm_Freiman_cf_convergence
import Definitions.Def_Freiman_gapCertificateData

open Freiman

theorem solution (hsound : GapCertificateSoundness) (h3 : gapCoverage gapForcingTree3) (h4 : gapCoverage gapForcingTree4) (hc3 : gapChecks gapLowerRows gapUpperRows .reduction gapForcingTree3) (hc4 : gapChecks gapLowerRows gapUpperRows .reduction gapForcingTree4) (a : ℤ → ℕ+) (hc : gapCapped a) (hl : gapLowerValid a gapLowerRows) (hu : gapUpperValid a gapUpperRows) (hw : gapWindow < localValue a 0) : gapReduced a 0 := by
  have hd : gapDigits a := gap_capped_digits a hc
  have hge : 3 ≤ (a 0 : ℕ) := by
    by_contra hn
    have hn2 : ((a 0 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (by omega : (a 0 : ℕ) ≤ 2)
    have hl1 := (cf_convergence (fun n : ℕ => a (0 - (n : ℤ) - 1))).2.2.2.1
    have hr1 := (cf_convergence (fun n : ℕ => a (0 + (n : ℤ) + 1))).2.2.2.1
    have h4 : (4 : ℝ) < gapWindow := by norm_num [gapWindow]
    unfold localValue at hw
    linarith
  have hle : (a 0 : ℕ) ≤ 4 := hd 0
  have ha : a 0 = 3 ∨ a 0 = 4 := by
    have ha : (a 0 : ℕ) = 3 ∨ (a 0 : ℕ) = 4 := by omega
    simpa only [← PNat.coe_inj, PNat.val_ofNat] using ha
  rcases ha with ha | ha
  · have hm : gapMatch a 0 (gapRoot gapForcingTree3) := by
      change gapMatch a 0 ⟨[3], 0⟩
      refine ⟨by decide, ?_⟩
      intro n hn
      change n < 1 at hn
      have hn0 : n = 0 := by simpa using (by omega : n = 0)
      subst n
      simpa using ha
    exact (hsound _ _ .reduction gapForcingTree3 a 0 hd hc hl hu h3 hc3 hm) hw
  · have hm : gapMatch a 0 (gapRoot gapForcingTree4) := by
      change gapMatch a 0 ⟨[4], 0⟩
      refine ⟨by decide, ?_⟩
      intro n hn
      change n < 1 at hn
      have hn0 : n = 0 := by simpa using (by omega : n = 0)
      subst n
      simpa using ha
    exact (hsound _ _ .reduction gapForcingTree4 a 0 hd hc hl hu h4 hc4 hm) hw

