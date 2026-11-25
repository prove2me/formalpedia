-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.MC.GI.term_valE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:50:17.087551+00:00
-- url     : https://prove2.me/submissions/e530c6cf-6962-4fa5-89e2-11d50150b0a0

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_TheoremMCB
import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_PartnerMeanProofs_GamIntC
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_GammaExpansion_IsPD_mul
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
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_mul
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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.MC Formalism.InvariantFactorPaths.MC.GI
open MvPolynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.gammaIntegralityLemmas
variable {p : ℕ} [hp : Fact p.Prime]
variable {N r : ℕ}
namespace Formalism.InvariantFactorPaths.MC.GI
theorem _root_.solution (LL : Letters (N + 1)) (hr : 1 ≤ r) (B : ℕ)
    (hB : Nat.log p (LL.total + LL.deg (Fin.last N) + r) ≤ B) (j a a' : ℕ)
    (hj : j ≤ LL.deg (Fin.last N)) (ha : a ≤ j) (ha' : a' ≤ j)
    (δ : Fin (N + 1 + 1) × Fin r →₀ ℕ)
    (hk : ∀ k : Fin N, δv δ (Fin.castSucc (Fin.castSucc k)) = LL.deg (Fin.castSucc k))
    (hW : δv δ (Fin.castSucc (Fin.last N)) = LL.deg (Fin.last N) - j)
    (hY : δv δ (Fin.last (N + 1)) = LL.total - (j - a))
    (d1 d2 : ℕ) (hd1 : padicValNat p a.factorial ≤ padicValNat p d1) (hd1' : d1 ≠ 0)
    (hd2 : padicValNat p a'.factorial ≤ padicValNat p d2) (hd2' : d2 ≠ 0) :
    -(kapE N r B : ℤ) + ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p (j - a).factorial : ℤ))) +
      ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p (j - a').factorial : ℤ))) -
      (padicValNat p (j.choose a * j.choose a' * d1 * d2 * a'.factorial *
        ∏ v : Fin (N + 1 + 1) × Fin r, (δ v).factorial) : ℤ) +
      (padicValNat p ((LL.deg (Fin.last N)).choose j * j.factorial ^ 2 * LL.total.factorial *
        ∏ i, (LL.deg i).factorial) : ℤ) ≤ 0 := by
  have hpp : p.Prime := hp.out
  have hF : ∀ n : ℕ, n.factorial ≠ 0 := fun n => Nat.factorial_ne_zero n
  have hmul : ∀ x y : ℕ, x ≠ 0 → y ≠ 0 → padicValNat p (x * y) = padicValNat p x + padicValNat p y :=
    fun x y hx hy => padicValNat.mul hx hy
  have hprod : ∀ {ι : Type} (s : Finset ι) (f : ι → ℕ), (∀ i, f i ≠ 0) →
      padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
    intro ι s f hf
    classical
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro x s hx ih
      rw [Finset.prod_insert hx, Finset.sum_insert hx,
        hmul _ _ (hf x) (Finset.prod_ne_zero_iff.2 (fun i _ => hf i)), ih]
  have hlog : ∀ m, m ≤ LL.total + LL.deg (Fin.last N) + r → Nat.log p m ≤ B :=
    fun m hm => (Nat.log_mono_right hm).trans hB
  have hch : ∀ n k : ℕ, n ≤ LL.total + LL.deg (Fin.last N) + r → padicValNat p (n.choose k) ≤ B := by
    intro n k hn
    rw [← Nat.factorization_def _ hpp]
    exact Nat.factorization_choose_le_log.trans (hlog n hn)
  have hsplit : ∀ n k : ℕ, k ≤ n → padicValNat p n.factorial =
      padicValNat p (n.choose k) + padicValNat p k.factorial + padicValNat p (n - k).factorial := by
    intro n k hk
    rw [← Nat.choose_mul_factorial_mul_factorial hk,
      hmul _ _ (mul_ne_zero (Nat.choose_pos hk).ne' (hF _)) (hF _),
      hmul _ _ (Nat.choose_pos hk).ne' (hF _)]
  have hgroup : ∀ (s : Finset (Fin r)) (x : Fin r → ℕ),
      ∑ i ∈ s, x i ≤ LL.total + LL.deg (Fin.last N) + r →
      padicValNat p (∑ i ∈ s, x i).factorial ≤ ∑ i ∈ s, padicValNat p (x i).factorial + s.card * B := by
    intro s x
    refine Finset.induction_on s ?_ ?_
    · intro _; simp
    · intro y s hy ih hle
      rw [Finset.sum_insert hy] at hle
      rw [Finset.sum_insert hy, Finset.sum_insert hy, Finset.card_insert_of_notMem hy]
      have h1 := hsplit (x y + ∑ i ∈ s, x i) (x y) (Nat.le_add_right _ _)
      rw [Nat.add_sub_cancel_left] at h1
      have h2 := hch (x y + ∑ i ∈ s, x i) (x y) hle
      have h3 := ih (le_trans (Nat.le_add_left _ _) hle)
      rw [h1]
      nlinarith
  have hT : ∀ i, LL.deg i ≤ LL.total := fun i => by
    unfold Letters.total
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hD : LL.deg (Fin.last N) ≤ LL.total := hT _
  have hδv : ∀ k, δv δ k = ∑ ρ, δ (k, ρ) := fun _ => rfl
  have hgδ : ∀ k, δv δ k ≤ LL.total + LL.deg (Fin.last N) + r →
      padicValNat p (δv δ k).factorial ≤ ∑ ρ, padicValNat p (δ (k, ρ)).factorial + r * B := by
    intro k hk
    rw [hδv] at hk ⊢
    have h := hgroup Finset.univ (fun ρ => δ (k, ρ)) hk
    rwa [Finset.card_univ, Fintype.card_fin] at h
  have hC1 : j.choose a ≠ 0 := (Nat.choose_pos ha).ne'
  have hC2 : j.choose a' ≠ 0 := (Nat.choose_pos ha').ne'
  have hCDj : (LL.deg (Fin.last N)).choose j ≠ 0 := (Nat.choose_pos hj).ne'
  have hPne : ∏ v : Fin (N + 1 + 1) × Fin r, (δ v).factorial ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun v _ => hF _)
  have hP2 : ∏ i, (LL.deg i).factorial ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => hF _)
  have P1 : padicValNat p (j.choose a * j.choose a' * d1 * d2 * a'.factorial *
        ∏ v : Fin (N + 1 + 1) × Fin r, (δ v).factorial) =
      padicValNat p (j.choose a) + padicValNat p (j.choose a') + padicValNat p d1 + padicValNat p d2 +
        padicValNat p a'.factorial +
        ∑ k : Fin (N + 1 + 1), ∑ ρ : Fin r, padicValNat p (δ (k, ρ)).factorial := by
    rw [hmul _ _ (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hC1 hC2) hd1') hd2') (hF _)) hPne,
      hmul _ _ (mul_ne_zero (mul_ne_zero (mul_ne_zero hC1 hC2) hd1') hd2') (hF _),
      hmul _ _ (mul_ne_zero (mul_ne_zero hC1 hC2) hd1') hd2',
      hmul _ _ (mul_ne_zero hC1 hC2) hd1', hmul _ _ hC1 hC2, hprod _ _ (fun v => hF _),
      Fintype.sum_prod_type]
  have P2 : padicValNat p ((LL.deg (Fin.last N)).choose j * j.factorial ^ 2 * LL.total.factorial *
        ∏ i, (LL.deg i).factorial) =
      padicValNat p ((LL.deg (Fin.last N)).choose j) +
        (padicValNat p j.factorial + padicValNat p j.factorial) +
        padicValNat p LL.total.factorial + ∑ i, padicValNat p (LL.deg i).factorial := by
    rw [hmul _ _ (mul_ne_zero (mul_ne_zero hCDj (pow_ne_zero _ (hF _))) (hF _)) hP2,
      hmul _ _ (mul_ne_zero hCDj (pow_ne_zero _ (hF _))) (hF _),
      hmul _ _ hCDj (pow_ne_zero _ (hF _)), sq, hmul _ _ (hF _) (hF _), hprod _ _ (fun i => hF _)]
  have S1 : ∑ k : Fin (N + 1 + 1), ∑ ρ : Fin r, padicValNat p (δ (k, ρ)).factorial =
      ∑ k : Fin N, ∑ ρ : Fin r, padicValNat p (δ (Fin.castSucc (Fin.castSucc k), ρ)).factorial +
        ∑ ρ : Fin r, padicValNat p (δ (Fin.castSucc (Fin.last N), ρ)).factorial +
        ∑ ρ : Fin r, padicValNat p (δ (Fin.last (N + 1), ρ)).factorial := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have S2 : ∑ i, padicValNat p (LL.deg i).factorial =
      ∑ k : Fin N, padicValNat p (LL.deg (Fin.castSucc k)).factorial +
        padicValNat p (LL.deg (Fin.last N)).factorial := by
    rw [Fin.sum_univ_castSucc]
  have G1 : ∑ k : Fin N, padicValNat p (LL.deg (Fin.castSucc k)).factorial ≤
      ∑ k : Fin N, ∑ ρ : Fin r, padicValNat p (δ (Fin.castSucc (Fin.castSucc k), ρ)).factorial +
        N * (r * B) := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N))) (fun k _ => by
      have hk' := hgδ (Fin.castSucc (Fin.castSucc k)) (by rw [hk k]; have := hT (Fin.castSucc k); omega)
      rw [hk k] at hk'
      exact hk')
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
    exact h
  have GW := hgδ (Fin.castSucc (Fin.last N)) (by rw [hW]; omega)
  rw [hW] at GW
  have GY := hgδ (Fin.last (N + 1)) (by rw [hY]; omega)
  rw [hY] at GY
  have hja : j - a ≤ LL.total := by omega
  have E1 := hsplit j a ha
  have E2 := hsplit j a' ha'
  have E3 := hsplit (LL.deg (Fin.last N)) j hj
  have E4 := hsplit LL.total (j - a) hja
  have B1 := hch (LL.deg (Fin.last N)) j (by omega)
  have B2 := hch LL.total (j - a) (by omega)
  have B3 := hch j a' (by omega)
  rw [P1, P2, S1, S2]
  unfold kapE
  push_cast
  nlinarith
end Formalism.InvariantFactorPaths.MC.GI
