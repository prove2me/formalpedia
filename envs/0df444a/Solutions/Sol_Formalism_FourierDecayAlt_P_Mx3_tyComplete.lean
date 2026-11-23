-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx3.tyComplete
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:02.517274+00:00
-- url     : https://prove2.me/submissions/c2561881-fc7f-42bc-b040-4285d9dadfec

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_rho_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_val_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_lo_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_floor_of_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx3
namespace Formalism.FourierDecayAlt.P.Mx3
theorem _root_.solution : TyComplete := by
  intro P hP
  constructor
  · intro ρ hI hint
    have key : ∀ i ∈ Icc 1 (P.k - 1), 0 ≤ ρ i - P.lo i ∧ ρ i - P.lo i ≤ P.hi i - P.lo i ∧
        ((⌊ρ i - P.lo i⌋₊ : ℕ) : ℝ) = ρ i - P.lo i := by
      intro i hi
      have b := hI i hi
      have c1 : P.lo i ≤ ρ i := by
        unfold Par.lo
        have : max (P.u (i + 1)) (P.u' (i + 1)) ≤ ρ i - 1 / 2 := max_le (by linarith [b.2.2.1]) (by linarith [b.2.2.2])
        linarith
      have c2 : ρ i ≤ P.hi i := by
        unfold Par.hi
        have := le_min (a := P.u i) (b := P.u' i) (c := ρ i + 1 / 2) b.1 b.2.1
        linarith
      obtain ⟨a, ha⟩ := lo_int P hP i hi
      obtain ⟨n, hn⟩ := hint i hi
      exact ⟨by linarith, by linarith, floor_of_int _ (by linarith) (n - a) (by push_cast; linarith)⟩
    refine ⟨fun i => ⟨⌊ρ ((i : ℕ) + 1) - P.lo ((i : ℕ) + 1)⌋₊, ?_⟩, ?_⟩
    · have hi : (i : ℕ) + 1 ∈ Icc 1 (P.k - 1) := Finset.mem_Icc.2 ⟨by omega, by have := i.2; omega⟩
      exact Nat.lt_succ_of_le (Nat.floor_le_floor (key _ hi).2.1)
    · intro i hi
      have h := Finset.mem_Icc.1 hi
      rw [rho_eq P _ i h]
      have e : i - 1 + 1 = i := by omega
      simp only [e]
      rw [(key i hi).2.2]; ring
  · intro π π' h
    funext i
    apply Fin.ext
    have hi : (i : ℕ) + 1 ∈ Icc 1 (P.k - 1) := Finset.mem_Icc.2 ⟨by omega, by have := i.2; omega⟩
    have h1 := h _ hi
    rw [rho_eq P π _ (Finset.mem_Icc.1 hi), rho_eq P π' _ (Finset.mem_Icc.1 hi)] at h1
    have h2 : (((π ⟨(i : ℕ) + 1 - 1, by have := i.2; omega⟩ : Fin _) : ℕ) : ℝ) = (((π' ⟨(i : ℕ) + 1 - 1, by have := i.2; omega⟩ : Fin _) : ℕ) : ℝ) := by
      linarith
    have h3 : ((π ⟨(i : ℕ) + 1 - 1, by have := i.2; omega⟩ : Fin _) : ℕ) = ((π' ⟨(i : ℕ) + 1 - 1, by have := i.2; omega⟩ : Fin _) : ℕ) := by
      exact_mod_cast h2
    rw [val_congr P π _ i (Fin.ext (by simp)), val_congr P π' _ i (Fin.ext (by simp))] at h3
    exact h3
end Formalism.FourierDecayAlt.P.Mx3
