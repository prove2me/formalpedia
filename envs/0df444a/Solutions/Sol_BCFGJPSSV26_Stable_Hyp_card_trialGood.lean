-- Prove2me | solution 1 for BCFGJPSSV26.Stable.Hyp.card_trialGood
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:20:32.124975+00:00
-- url     : https://prove2.me/submissions/5c6ca997-1eb1-4f3c-ba9a-ce048adcc593

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClientSampling
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingAnalysis
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Submod
public import Definitions.Def_BCFGJPSSV26_Stable_Final_Combine
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Trial
import all Definitions.Def_BCFGJPSSV26_Stable_Alg_Trial
public import Theorems.Thm_BCFGJPSSV26_Stable_Hyp_card_clientWitness
public import Theorems.Thm_BCFGJPSSV26_Stable_Hyp_card_clusterWitness
public import Theorems.Thm_BCFGJPSSV26_Stable_Hyp_exists_partition
public import Theorems.Thm_BCFGJPSSV26_Stable_Partition_card_colorEvent
public import Theorems.Thm_BCFGJPSSV26_Stable_Partition_costF_candidate_le
public import Theorems.Thm_BCFGJPSSV26_Stable_Partition_min_le_bound
public import Theorems.Thm_BCFGJPSSV26_Stable_candidate_spec

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace Ctx

variable (X : Ctx)

end Ctx

/-- **Good outcomes make a good candidate**: for the outcome `Λ₁` of the client
sampling, `(LS', dums)` of the cluster sampling and a coloring `col` satisfying the color event,
the local search or the candidate of some guess is within the bound. -/
theorem Hyp.exists_good_candidate {X : Ctx} (H : Hyp X) {LS : List ℕ}
    (hLS : X.I.centers LS = X.S) (hnd : LS.Nodup) (hm : ∀ i ∈ LS, i < X.I.m) {B : ℕ}
    (hB : X.P.N ^ X.s ≤ B) {Λ₁ dums : List DumQ} (hval₁ : (toRaw X.I).ValidDums Λ₁)
    (hval₂ : (toRaw X.I).ValidDums dums) {LS' : List ℕ} (hLS'nd : LS'.Nodup)
    (hLS'm : ∀ i ∈ LS', i < X.I.m) {col : List Bool} (hcol_len : col.length = LS'.length)
    (w₁ : ClientWitness X (toDums X.I Λ₁))
    (w₂ : ClusterWitness w₁ (X.I.centers LS') (toDums X.I dums)) (Q : Partition w₂)
    (hcol : Q.ColorEvent (X.I.centers (redOf LS' col)) (X.I.centers (blueOf LS' col))) :
    X.I.costF (X.I.centers (sanitizeK X.I.m X.I.k LS)) ≤ bound X.P X.I ∨
      ∃ p' ≤ X.s, ∃ T, candidate X.P.N (toRaw X.I) X.s B LS' (Λ₁ ++ dums) col p' = some T ∧
        X.I.costF (X.I.centers (sanitizeK X.I.m X.I.k T)) ≤ bound X.P X.I := by
  classical
  have hval : (toRaw X.I).ValidDums (Λ₁ ++ dums) := by
    intro l hl
    rcases List.mem_append.1 hl with h | h
    · exact hval₁ l h
    · exact hval₂ l h
  have hΛeq : toDums X.I (Λ₁ ++ dums) = toDums X.I Λ₁ ++ toDums X.I dums := toDums_append _ _ _
  have hlenΛ : (toDums X.I Λ₁).length + (toDums X.I dums).length = (Λ₁ ++ dums).length := by
    rw [← List.length_append, ← hΛeq, Raw.length_toDums hval]
  -- the guess `|O_P|`
  have hρ : (Λ₁ ++ dums).length + Q.OP.card ≤ X.s := by
    have := Q.card_OLam_add_OP_le H
    rw [List.length_append, hlenΛ] at this
    exact this
  have hz : Q.z = (LS'.length + ((Λ₁ ++ dums).length + Q.OP.card)) - X.I.k := by
    unfold Partition.z
    rw [Instance.card_centers hLS'nd hLS'm, hlenΛ]
  have hball : ∀ l ∈ Λ₁ ++ dums, (toRaw X.I).ballQ l ≠ [] := by
    refine Raw.ballQ_ne_nil hval ?_
    obtain ⟨o, ho, -⟩ := Q.exists_ball_choice H
    rw [hΛeq]
    intro l hl
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hl
    exact ⟨o i, ho i⟩
  have hzc : Q.Zstar.card = Q.z := Q.Zstar_card
  have hzred : (LS'.length + ((Λ₁ ++ dums).length + Q.OP.card)) - X.I.k ≤
      (redOf LS' col).length := by
    rw [← hz, ← hzc]
    exact (card_le_card hcol.1).trans (Instance.card_centers_le _)
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1
    (candidate_isSome (I := X.I) (N := X.P.N) (B := B) hρ hzred hball)
  have hB' : X.P.N ^ ((Λ₁ ++ dums).length + Q.OP.card) ≤ B :=
    (Nat.pow_le_pow_right X.P.N_pos hρ).trans hB
  obtain ⟨hTnd, hTm, hTk, Y, Zh, hTeq, hY, hZ, hZc, hZs, hG⟩ :=
    candidate_spec H.valid X.P.N_pos hLS'nd hLS'm hval hcol_len hB' hT
  rw [hΛeq] at hY hZs hG
  rw [← hz] at hZc hZs hG
  obtain ⟨hred, hblue⟩ := centers_red_blue (I := X.I) hLS'nd hcol_len
  have hcT := Q.costF_candidate_le H hred hblue hcol hY hZ hZc hZs hG
  rw [← hTeq] at hcT
  -- the bound
  have hopt : 0 ≤ X.opt := H.opt_pos.le
  have hfin : (1 + eta + 100 * X.ε) * X.opt ≤ bound X.P X.I := by
    unfold bound eta
    have hN := X.P.N_pos'
    have hε : X.ε = 1 / X.P.N := rfl
    have h1 : (1 : ℝ) + 89 / 100 + 100 * X.ε ≤ 1.89 + 1000 / X.P.N := by
      rw [hε]
      have : (100 : ℝ) * (1 / X.P.N) ≤ 1000 / X.P.N := by
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right (by norm_num) hN.le
      norm_num at this ⊢
      linarith
    exact mul_le_mul_of_nonneg_right h1 hopt
  rcases Q.min_le_bound H hcT with h | h
  · left
    have hLSk : LS.length ≤ X.I.k := by
      rw [← Instance.card_centers hnd hm, hLS, H.alo.1]
    refine (costF_sanitizeK_le H.valid hnd hm hLSk).trans ?_
    rw [hLS]
    exact h.trans hfin
  · exact .inr ⟨Q.OP.card, by omega, T, hT,
      (costF_sanitizeK_le H.valid hTnd hTm hTk).trans (h.trans hfin)⟩

/-- **Good outcomes make a good trial.** -/
theorem Hyp.trialCands_good {X : Ctx} (H : Hyp X) {LS : List ℕ} (hLS : X.I.centers LS = X.S)
    (hnd : LS.Nodup) (hm : ∀ i ∈ LS, i < X.I.m) {B : ℕ} (hB : X.P.N ^ X.s ≤ B)
    {ch₁ ch₂ ch₃ : ℕ → ℕ} (w₁ : ClientWitness X (toDums X.I (X.csOut LS ch₁)))
    (w₂ : ClusterWitness w₁ (X.I.centers (ksLS' LS (X.ksOut LS ch₁ ch₂)))
      (toDums X.I (X.ksOut LS ch₁ ch₂).dums)) (Q : Partition w₂)
    (hcol : Q.ColorEvent
      (X.I.centers (redOf (ksLS' LS (X.ksOut LS ch₁ ch₂))
        (colors X.b (ksLS' LS (X.ksOut LS ch₁ ch₂)) ch₃)))
      (X.I.centers (blueOf (ksLS' LS (X.ksOut LS ch₁ ch₂))
        (colors X.b (ksLS' LS (X.ksOut LS ch₁ ch₂)) ch₃)))) :
    ∃ T ∈ LS :: trialCands X.P.N (toRaw X.I) X.L LS B ch₁ ch₂ ch₃,
      X.I.costF (X.I.centers (sanitizeK X.I.m X.I.k T)) ≤ bound X.P X.I := by
  have hval₂ : (toRaw X.I).ValidDums (X.ksOut LS ch₁ ch₂).dums := by
    intro l hl
    obtain ⟨i, hi, h⟩ := ksRun_dums hm _ _ _ _ _ l hl
    have := hm i hi
    rw [h]
    change X.I.n + i < X.I.n + X.I.m
    omega
  rcases H.exists_good_candidate hLS hnd hm hB (csRun_valid H.one_le_n _ _ _ _ _) hval₂
    (hnd.filter _) (fun i hi ↦ hm i (List.mem_of_mem_filter hi)) (by simp [colors, ksLS']) w₁ w₂ Q
    hcol with h | ⟨p', hp', T, hT, h⟩
  · exact ⟨LS, List.mem_cons_self, h⟩
  · exact ⟨T, List.mem_cons_of_mem _
      (List.mem_filterMap.2 ⟨p', List.mem_range.2 (Nat.lt_succ_of_le hp'), hT⟩), h⟩

open Classical in
/-- **A trial is good with probability at least `q`.** -/
theorem Hyp.card_trialGood {X : Ctx} (H : Hyp X) {LS : List ℕ} (hLS : X.I.centers LS = X.S)
    (hnd : LS.Nodup) (hm : ∀ i ∈ LS, i < X.I.m) {B : ℕ} (hB : X.P.N ^ X.s ≤ B) :
    X.P.q X.L * ((2 : ℝ) ^ X.b) ^ Par.Ctr X.P.N X.L X.I.k ≤
      (univ.filter fun v : Fin (Par.Ctr X.P.N X.L X.I.k) → Fin (2 ^ X.b) ↦
        TrialGood X.P X.I X.L LS B (toCh v)).card := by
  have hK : (Fintype.card (Fin (2 ^ X.b)) : ℝ) = (2 : ℝ) ^ X.b := by simp
  have hLSk : LS.length ≤ X.I.k := by
    rw [← Instance.card_centers hnd hm, hLS, H.alo.1]
  -- the client sampling, then the cluster sampling
  let P₁ : (Fin (6 * X.s) → Fin (2 ^ X.b)) → Prop := fun u ↦
    Nonempty (ClientWitness X (toDums X.I (X.csOut LS (toCh u))))
  let P₂ : (Fin (6 * X.s) → Fin (2 ^ X.b)) → (Fin (Par.M₂ X.P.N X.L) → Fin (2 ^ X.b)) → Prop :=
    fun u v ↦ ∃ w₁ : ClientWitness X (toDums X.I (X.csOut LS (toCh u))),
      Nonempty (ClusterWitness w₁ (X.I.centers (ksLS' LS (X.ksOut LS (toCh u) (toCh v))))
        (toDums X.I (X.ksOut LS (toCh u) (toCh v)).dums))
  have h12 := card_append_ge P₁ P₂ (q₁ := X.P.q₁ ^ (2 * X.s))
    (q₂ := X.P.q₂ ^ Par.M₂ X.P.N X.L) (by unfold Prm.q₂; positivity)
    (by rw [hK]; exact H.card_clientWitness hLS hnd hm)
    (fun u hu ↦ by
      obtain ⟨w₁⟩ := hu
      have h := H.card_clusterWitness hLS hnd hm (csRun_valid H.one_le_n _ _ _ _ _) w₁
      rw [hK]
      refine h.trans ?_
      exact_mod_cast card_le_card fun v hv ↦ by
        simp only [mem_filter, mem_univ, true_and] at hv ⊢
        exact ⟨w₁, hv⟩)
  -- the coloring
  let P₁₂ : (Fin (6 * X.s + Par.M₂ X.P.N X.L) → Fin (2 ^ X.b)) → Prop := fun z ↦
    P₁ (fun i ↦ z (Fin.castAdd _ i)) ∧ P₂ (fun i ↦ z (Fin.castAdd _ i)) (fun i ↦ z (Fin.natAdd _ i))
  let P₃ : (Fin (6 * X.s + Par.M₂ X.P.N X.L) → Fin (2 ^ X.b)) → (Fin X.I.k → Fin (2 ^ X.b)) →
      Prop := fun z u ↦
    ∃ (w₁ : ClientWitness X (toDums X.I (X.csOut LS (toCh fun i ↦ z (Fin.castAdd _ i)))))
      (w₂ : ClusterWitness w₁ (X.I.centers (ksLS' LS (X.ksOut LS (toCh fun i ↦ z (Fin.castAdd _ i))
        (toCh fun i ↦ z (Fin.natAdd _ i)))))
        (toDums X.I (X.ksOut LS (toCh fun i ↦ z (Fin.castAdd _ i))
          (toCh fun i ↦ z (Fin.natAdd _ i))).dums))
      (Q : Partition w₂),
      Q.ColorEvent
        (X.I.centers (redOf (ksLS' LS (X.ksOut LS (toCh fun i ↦ z (Fin.castAdd _ i))
          (toCh fun i ↦ z (Fin.natAdd _ i))))
          (colors X.b (ksLS' LS (X.ksOut LS (toCh fun i ↦ z (Fin.castAdd _ i))
            (toCh fun i ↦ z (Fin.natAdd _ i)))) (toCh u))))
        (X.I.centers (blueOf (ksLS' LS (X.ksOut LS (toCh fun i ↦ z (Fin.castAdd _ i))
          (toCh fun i ↦ z (Fin.natAdd _ i))))
          (colors X.b (ksLS' LS (X.ksOut LS (toCh fun i ↦ z (Fin.castAdd _ i))
            (toCh fun i ↦ z (Fin.natAdd _ i)))) (toCh u))))
  have h123 := card_append_ge P₁₂ P₃ (q₁ := X.P.q₁ ^ (2 * X.s) * X.P.q₂ ^ Par.M₂ X.P.N X.L)
    (q₂ := (1 / 4) ^ X.s) (by positivity) (by convert h12)
    (fun z hz ↦ by
      obtain ⟨-, w₁, ⟨w₂⟩⟩ := hz
      obtain ⟨Q⟩ := H.exists_partition w₁ w₂
      have h := Q.card_colorEvent H (hnd.filter _)
        (fun i hi ↦ hm i (List.mem_of_mem_filter hi)) ((List.length_filter_le _ _).trans hLSk)
      rw [hK]
      refine h.trans ?_
      exact_mod_cast card_le_card fun u hu ↦ by
        simp only [mem_filter, mem_univ, true_and] at hu ⊢
        exact ⟨w₁, w₂, Q, hu⟩)
  rw [hK] at h123
  have hq := H.q_le_prod
  refine (mul_le_mul_of_nonneg_right hq (by positivity)).trans (h123.trans ?_)
  exact_mod_cast card_le_card fun z hz ↦ by
    simp only [mem_filter, mem_univ, true_and] at hz
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    obtain ⟨-, w₁, w₂, Q, hcol⟩ := hz
    unfold TrialGood
    rw [trial_toCh]
    exact H.trialCands_good hLS hnd hm hB w₁ w₂ Q hcol

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.Hyp.card_trialGood := @BCFGJPSSV26.Stable.Hyp.card_trialGood
