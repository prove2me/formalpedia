-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.corollary_lower_estimate_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:43.120884+00:00
-- url     : https://prove2.me/submissions/de2f2646-e7ba-4e82-949e-18778b13738f

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_moment_ratio_telescoping

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
open scoped ENNReal
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.MomentDownwardBound := by
  intro Ω _ μ _ r q l T R hm hpos hT hR hl hc a
  have ha : a.val ≤ r := Nat.lt_succ_iff.1 a.isLt
  let M : ℕ → Ω → ℝ := fun i ω => l ⟨min (a.val + i) r, by omega⟩ ω
  have hq : (r - a.val) * q ≤ (r + 1) * q := Nat.mul_le_mul_right _ (by omega)
  have key := moment_ratio_telescoping μ M (r - a.val) q (fun _ => R) (fun i => hm _) (fun i ω => hpos _ _) (fun _ => hR)
    (by
      intro i hi
      have hk : a.val + i < r := by omega
      have e1 : (⟨min (a.val + (i + 1)) r, by omega⟩ : Fin (r + 1)) = (⟨a.val + i, hk⟩ : Fin r).succ :=
        Fin.ext (by simp; omega)
      have e2 : (⟨min (a.val + i) r, by omega⟩ : Fin (r + 1)) = (⟨a.val + i, hk⟩ : Fin r).castSucc :=
        Fin.ext (by simp; omega)
      simp only [M, e1, e2]
      exact hc _ _ hq)
  have ea : (⟨min (a.val + 0) r, by omega⟩ : Fin (r + 1)) = a := Fin.ext (by simp; omega)
  have er : (⟨min (a.val + (r - a.val)) r, by omega⟩ : Fin (r + 1)) = Fin.last r := Fin.ext (by simp; omega)
  simp only [M, ea, er, prod_const, card_range] at key
  rw [← pow_mul] at key
  refine le_trans (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_) key
  have h1 : 1 ≤ l (Fin.last r) ω := by
    have h2 := hl ω
    have h3 := hpos (Fin.last r) ω
    nlinarith
  have h4 := hpos a ω
  apply pow_le_pow_left₀ (by positivity)
  rw [div_eq_mul_inv]
  exact le_mul_of_one_le_left (by positivity) h1
end Formalism.HermitianLatticeCounting.P
