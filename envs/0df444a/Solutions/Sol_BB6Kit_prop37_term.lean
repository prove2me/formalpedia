-- Prove2me | solution 1 for BB6Kit.prop37_term
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-24T06:59:26.968456+00:00
-- url     : https://prove2.me/submissions/5051a2a4-c0f6-4d14-921e-be5692db9804

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit
import Definitions.Def_BB6Psi
import Definitions.Def_BB6Theta
import Theorems.Thm_BB6Kit_schwarz_order
import Theorems.Thm_BB6Kit_prop37_order
import Theorems.Thm_BB6Kit_prop37_max
import Theorems.Thm_BB6Kit_prop37_numeric

open Finset

theorem solution (K L R S T N b1 b2 b3 α1 α2 α3 : ℕ) (ρ : ℝ)
    (hK : 3 ≤ K) (hL : 5 ≤ L) (hN : N = K * (K + 1) * L / 2) (hRST : N ≤ R * S * T)
    (hα1 : 1 < α1) (hα2 : 1 < α2) (hα3 : 1 < α3) (hind : BB6Kit.MultIndep α1 α2 α3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hgcd : Nat.gcd (Nat.gcd b1 b2) b3 = 1)
    (hΛ : ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) ≠ 0) (hρ : 2 ≤ ρ)
    (kml rst : Fin N → ℕ × ℕ × ℕ) (hrows : BB6Kit.RowsOK K L N kml) (hcols : BB6Kit.ColsOK R S T N rst)
    (hsmall : BB6Kit.lamPrime L T b3 ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) < ρ ^ (-((K : ℝ) * L))) :
    ∀ I : Finset (Fin N),
      BB6Kit.lamPrime L T b3 ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) ^ (N - I.card) * ‖BB6Psi.psi N L R S T (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3) b3 α1 α2 ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) kml rst I 1‖ <
        Real.exp (ρ * (BB6Kit.GK N L R S T R * Real.log (α1 : ℝ) + BB6Kit.GK N L R S T S * Real.log (α2 : ℝ) + BB6Kit.GK N L R S T T * Real.log (α3 : ℝ)) + Real.log (N.factorial : ℝ) +
        (N : ℝ) * ((K : ℝ) - 1) / 3 * Real.log (BB6Kit.bK K R S T (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3)) -
        (N : ℝ) ^ 2 / (2 * (K : ℝ)) * (1 - 2 / (3 * (L : ℝ)) - 2 / (3 * (K : ℝ) * L) - 1 / (3 * (L : ℝ) ^ 2) -
          16 / (3 * (K : ℝ) ^ 2 * L)) * Real.log ρ + 0.001) := by
  intro I
  obtain ⟨hdiff, hvan⟩ := BB6Kit.prop37_order K L R S T N b1 b2 b3 α1 α2 α3 hK hL hN hRST hα1 hα2 hα3
    hb1 hb2 hb3 hΛ kml rst hrows hcols I
  have hmax := BB6Kit.prop37_max K L R S T N b1 b2 b3 α1 α2 α3 ρ hK hL hN hRST hα1 hα2 hα3
    hb1 hb2 hb3 hΛ kml rst hrows hcols (by linarith) I
  have hnum := BB6Kit.prop37_numeric K L R S T N b1 b2 b3 α1 α2 α3 ρ hK hL hN hRST hα1 hα2 hα3 hind
    hb1 hb2 hb3 hgcd hΛ hρ kml rst hrows hcols hsmall I
  have hs := BB6Kit.schwarz_order _ hdiff _ hvan ρ _ (by linarith) hmax
  have hLp : 0 ≤ BB6Kit.lamPrime L T b3 ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) := by
    unfold BB6Kit.lamPrime; positivity
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hs (pow_nonneg hLp _)) hnum
