-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.move_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:49:16.335035+00:00
-- url     : https://prove2.me/submissions/827edb22-4d76-44b5-92b0-f3455ef7e66b

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjection
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjectionPos
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (i0 : Fin N) (t : Fin r) (d : ℕ) (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hbase : ∀ m : Fin N × Fin r →₀ ℕ, (∀ c, c ≠ t → m (i0, c) = 0) → m (i0, t) = d →
      monomial m (1 : ℚ_[p]) ∈ S)
    (hst : ∀ a, ∀ x ∈ S, X (i0, a) * pderiv (i0, t) x ∈ S) :
    ∀ (n : ℕ) (m : Fin N × Fin r →₀ ℕ), m (i0, t) + n = d → ∑ c, m (i0, c) = d →
      monomial m (1 : ℚ_[p]) ∈ S := by
  intro n
  induction n with
  | zero =>
    intro m hm hs
    refine hbase m (fun c hc => ?_) (by omega)
    have h1 := Finset.add_sum_erase Finset.univ (fun c => m (i0, c)) (Finset.mem_univ t)
    have h2 : ∑ x ∈ Finset.univ.erase t, m (i0, x) = 0 := by omega
    exact Finset.sum_eq_zero_iff.mp h2 c (Finset.mem_erase.mpr ⟨hc, Finset.mem_univ c⟩)
  | succ n ih =>
    intro m hm hs
    obtain ⟨a, hat, ha⟩ : ∃ a, a ≠ t ∧ m (i0, a) ≠ 0 := by
      by_contra hne
      push_neg at hne
      have hsum : ∑ c, m (i0, c) = m (i0, t) :=
        Finset.sum_eq_single t (fun c _ hc => hne c hc) (fun hn => absurd (Finset.mem_univ t) hn)
      omega
    obtain ⟨m', hm'⟩ : ∃ m' : Fin N × Fin r →₀ ℕ,
        m' = m - Finsupp.single (i0, a) 1 + Finsupp.single (i0, t) 1 := ⟨_, rfl⟩
    have hle : Finsupp.single (i0, a) 1 ≤ m := by
      rw [Finsupp.single_le_iff]
      omega
    have heq : m' + Finsupp.single (i0, a) 1 = m + Finsupp.single (i0, t) 1 := by
      rw [hm', add_right_comm, tsub_add_cancel_of_le hle]
    have key : ∀ (f : Fin N × Fin r →₀ ℕ) (b : Fin r),
        ∑ c, ((f + Finsupp.single (i0, b) 1 : Fin N × Fin r →₀ ℕ)) (i0, c) = ∑ c, f (i0, c) + 1 := by
      intro f b
      simp [Finsupp.single_apply, Finset.sum_add_distrib]
    have hsum : ∑ c, m' (i0, c) = d := by
      have h3 := congrArg (fun f : Fin N × Fin r →₀ ℕ => ∑ c, f (i0, c)) heq
      simp only [key] at h3
      omega
    have ht : m' (i0, t) = m (i0, t) + 1 := by
      have h3 := congrArg (fun f : Fin N × Fin r →₀ ℕ => f (i0, t)) heq
      simp [Finsupp.single_apply, hat] at h3
      omega
    have hmem := ih m' (by omega) hsum
    have hX := hst a _ hmem
    have he : Finsupp.single (i0, a) 1 + (m' - Finsupp.single (i0, t) 1) = m := by
      rw [hm', add_tsub_cancel_right, add_tsub_cancel_of_le hle]
    have hcalc : X (i0, a) * pderiv (i0, t) (monomial m' (1 : ℚ_[p])) =
        ((m (i0, t) + 1 : ℕ) : ℚ_[p]) • monomial m (1 : ℚ_[p]) := by
      rw [pderiv_monomial, ← pow_one (X (i0, a)), ← monomial_single_add, he, smul_monomial, ht]
      simp
    rw [hcalc] at hX
    have hne : ((m (i0, t) + 1 : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m (i0, t))
    have h4 := S.smul_mem (((m (i0, t) + 1 : ℕ) : ℚ_[p]))⁻¹ hX
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h4
end Formalism.InvariantFactorPaths.L4
