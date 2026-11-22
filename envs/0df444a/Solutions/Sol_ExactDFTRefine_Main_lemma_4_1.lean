-- Prove2me | solution 1 for ExactDFTRefine.Main.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-22T23:02:35.331929+00:00
-- url     : https://prove2.me/submissions/9f01f6ab-7e64-44d9-b277-82078eb39661

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_Moments
import Theorems.Thm_ExactDFTRefine_Main_eq_12

namespace ExactDFTRefine.Main

private lemma splitBlock_moment_le (t : ℝ) (ht0 : 0 ≤ t)
    (J R : ℕ) (hJ : 0 < J) :
    moment t (splitBlock J R) ≤
      (R : ℝ) ^ t + 2 * (R : ℝ) * (J : ℝ) ^ (t - 1) := by
  have hJr : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hpow : (J : ℝ) ^ t = (J : ℝ) * (J : ℝ) ^ (t - 1) := by
    rw [show t = 1 + (t - 1) by ring, Real.rpow_add hJr]
    simp
  by_cases hRJ : R ≤ J
  · simp [splitBlock, hRJ, moment]
    positivity
  · have hJR : J < R := Nat.lt_of_not_ge hRJ
    have hmod : R % J < J := Nat.mod_lt _ hJ
    have hq : ((R / J : ℕ) : ℝ) * (J : ℝ) ≤ (R : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self R J
    have hq' : ((R / J : ℕ) : ℝ) * (J : ℝ) ^ t ≤
        (R : ℝ) * (J : ℝ) ^ (t - 1) := by
      calc
        ((R / J : ℕ) : ℝ) * (J : ℝ) ^ t =
            (((R / J : ℕ) : ℝ) * (J : ℝ)) * (J : ℝ) ^ (t - 1) := by
              rw [hpow]; ring
        _ ≤ (R : ℝ) * (J : ℝ) ^ (t - 1) :=
          mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hJr.le _)
    have hJ' : (J : ℝ) ^ t ≤ (R : ℝ) * (J : ℝ) ^ (t - 1) := by
      rw [hpow]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hJR.le)
        (Real.rpow_nonneg hJr.le _)
    have hRt : 0 ≤ (R : ℝ) ^ t := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hRp : 0 ≤ (R : ℝ) * (J : ℝ) ^ (t - 1) :=
      mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hJr.le _)
    by_cases hrem : R % J = 0
    · simp [moment, splitBlock, hRJ, hrem, nsmul_eq_mul]
      linarith
    · have hrem' : ((R % J : ℕ) : ℝ) ^ t ≤ (J : ℝ) ^ t := by
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hmod.le) ht0
      simp [moment, splitBlock, hRJ, hrem, nsmul_eq_mul]
      linarith

private lemma splitBlocks_moment_le (t : ℝ) (ht0 : 0 ≤ t)
    (J : ℕ) (hJ : 0 < J) (X : Multiset ℕ) :
    moment t (splitBlocks J X) ≤
      moment t X + 2 * (J : ℝ) ^ (t - 1) * moment 1 X := by
  induction X using Multiset.induction_on with
  | empty => simp [splitBlocks, moment]
  | cons R X ih =>
      have hR := splitBlock_moment_le t ht0 J R hJ
      rw [show splitBlocks J (R ::ₘ X) = splitBlock J R + splitBlocks J X by
        simp [splitBlocks, Multiset.cons_bind]]
      simp [moment] at ih hR ⊢
      nlinarith

private lemma splitBlock_moment_le_two (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (J B R : ℕ) (hJ : 0 < J) (hJB : J < B) (hRB : R ≤ B) :
    moment t (splitBlock J R) ≤ 2 * (B : ℝ) * (J : ℝ) ^ (t - 1) := by
  have hJr : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hBr : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (lt_trans hJ hJB)
  have hJp : 0 ≤ (J : ℝ) ^ (t - 1) := Real.rpow_nonneg hJr.le _
  have hpow : (J : ℝ) ^ t = (J : ℝ) * (J : ℝ) ^ (t - 1) := by
    rw [show t = 1 + (t - 1) by ring, Real.rpow_add hJr]
    simp
  have hBp : (B : ℝ) ^ t ≤ (B : ℝ) * (J : ℝ) ^ (t - 1) := by
    calc
      (B : ℝ) ^ t = (B : ℝ) * (B : ℝ) ^ (t - 1) := by
        rw [show t = 1 + (t - 1) by ring, Real.rpow_add hBr]
        simp
      _ ≤ (B : ℝ) * (J : ℝ) ^ (t - 1) := by
        apply mul_le_mul_of_nonneg_left _ hBr.le
        exact Real.rpow_le_rpow_of_nonpos hJr (by exact_mod_cast hJB.le) (by linarith)
  by_cases hRJ : R ≤ J
  · have hRt : (R : ℝ) ^ t ≤ (B : ℝ) ^ t :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hRB) ht0
    simp [splitBlock, hRJ, moment]
    nlinarith [mul_nonneg hBr.le hJp]
  · have hJR : J < R := Nat.lt_of_not_ge hRJ
    have hmod : R % J < J := Nat.mod_lt _ hJ
    have hq : ((R / J : ℕ) : ℝ) * (J : ℝ) ≤ (R : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self R J
    have hq' : ((R / J : ℕ) : ℝ) * (J : ℝ) ^ t ≤
        (R : ℝ) * (J : ℝ) ^ (t - 1) := by
      calc
        ((R / J : ℕ) : ℝ) * (J : ℝ) ^ t =
            (((R / J : ℕ) : ℝ) * (J : ℝ)) * (J : ℝ) ^ (t - 1) := by
              rw [hpow]; ring
        _ ≤ (R : ℝ) * (J : ℝ) ^ (t - 1) :=
          mul_le_mul_of_nonneg_right hq hJp
    have hJ' : (J : ℝ) ^ t ≤ (R : ℝ) * (J : ℝ) ^ (t - 1) := by
      rw [hpow]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hJR.le) hJp
    have hRBr : (R : ℝ) ≤ (B : ℝ) := by exact_mod_cast hRB
    have hRJp : (R : ℝ) * (J : ℝ) ^ (t - 1) ≤
        (B : ℝ) * (J : ℝ) ^ (t - 1) := mul_le_mul_of_nonneg_right hRBr hJp
    have hRnonneg : 0 ≤ (R : ℝ) * (J : ℝ) ^ (t - 1) :=
      mul_nonneg (Nat.cast_nonneg _) hJp
    by_cases hrem : R % J = 0
    · simp [moment, splitBlock, hRJ, hrem, nsmul_eq_mul]
      linarith
    · have hrem' : ((R % J : ℕ) : ℝ) ^ t ≤ (J : ℝ) ^ t := by
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hmod.le) ht0
      simp [moment, splitBlock, hRJ, hrem, nsmul_eq_mul]
      linarith

private lemma splitBlocks_moment_le_bounded (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (J B : ℕ) (hJ : 0 < J) (hJB : J < B) (Q : Multiset ℕ)
    (hQ : ∀ R ∈ Q, R ≤ B) :
    moment t (splitBlocks J Q) ≤
      2 * (Multiset.card Q : ℝ) * (B : ℝ) * (J : ℝ) ^ (t - 1) := by
  induction Q using Multiset.induction_on with
  | empty => simp [splitBlocks, moment]
  | cons R Q ih =>
      have hRB : R ≤ B := hQ R (Multiset.mem_cons_self R Q)
      have htail : ∀ S ∈ Q, S ≤ B := by
        intro S hS
        exact hQ S (Multiset.mem_cons_of_mem hS)
      have ih' := ih htail
      have hR := splitBlock_moment_le_two t ht0 ht1 J B R hJ hJB hRB
      rw [show splitBlocks J (R ::ₘ Q) = splitBlock J R + splitBlocks J Q by
        simp [splitBlocks, Multiset.cons_bind]]
      simp [moment, Multiset.card_cons] at ih' hR ⊢
      nlinarith

private lemma completionBlocks_card_le (B : ℕ) (X : Multiset ℕ) :
    Multiset.card (completionBlocks B X) ≤ Multiset.card X := by
  induction X using Multiset.induction_on with
  | empty => simp [completionBlocks]
  | cons K X ih =>
      by_cases hK : K < B
      · simp [completionBlocks, hK, Multiset.card_cons] at ih ⊢
        omega
      · simp [completionBlocks, hK, Multiset.card_cons] at ih ⊢
        omega

private lemma completionBlocks_rank_le {B R : ℕ} {X : Multiset ℕ}
    (hR : R ∈ completionBlocks B X) : R ≤ B := by
  simp only [completionBlocks, Multiset.mem_map, Multiset.mem_filter] at hR
  obtain ⟨K, ⟨_, hKB⟩, rfl⟩ := hR
  exact Nat.sub_le B K

private lemma completeTargets_moment_ge (t : ℝ) (ht0 : 0 ≤ t)
    (B : ℕ) (X : Multiset ℕ) :
    moment t X ≤ moment t (completeTargets B X) := by
  induction X using Multiset.induction_on with
  | empty => simp [completeTargets, moment]
  | cons K X ih =>
      have hK : (K : ℝ) ^ t ≤ ((max K B : ℕ) : ℝ) ^ t := by
        apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ ht0
        exact_mod_cast Nat.le_max_left K B
      simp [completeTargets, moment] at ih hK ⊢
      linarith

private lemma card_tensor (A B : Multiset ℕ) :
    Multiset.card (tensor A B) = Multiset.card A * Multiset.card B := by
  simp [tensor]

private lemma card_tpow (A : Multiset ℕ) (v : ℕ) :
    Multiset.card (tpow A v) = Multiset.card A ^ v := by
  induction v with
  | zero => simp [tpow]
  | succ v ih => simp [tpow, card_tensor, ih, pow_succ]

end ExactDFTRefine.Main

open ExactDFTRefine.Main

/-- **Lemma 4.1 (Completion and splitting)**, p. 5. For `0 ≤ t ≤ 1`, `v ≥ 1` and positive
integers `J < B`, the completed and split `v`-fold tensor unit of the Table 1 multisets satisfies
`M_t(P′) ≤ P_t^v + 2 J^{t-1} P_1^v + 2 |T|^v B J^{t-1}` and `M_t(T′) ≥ T_t^v` (13). -/
theorem solution (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (v : ℕ) (hv : 1 ≤ v) (J B : ℕ)
    (hJ : 0 < J) (hJB : J < B) :
    moment t (Pprime blocksP targetsT v J B) ≤
      moment t blocksP ^ v + 2 * (J : ℝ) ^ (t - 1) * moment 1 blocksP ^ v +
        2 * (Multiset.card targetsT : ℝ) ^ v * (B : ℝ) * (J : ℝ) ^ (t - 1) ∧
    moment t (Tprime targetsT v B) ≥ moment t targetsT ^ v := by
  have hP := splitBlocks_moment_le t ht0 J hJ (tpow blocksP v)
  have hQ := splitBlocks_moment_le_bounded t ht0 ht1 J B hJ hJB
    (completionBlocks B (tpow targetsT v)) (fun _ hR => completionBlocks_rank_le hR)
  rw [eq_12 t blocksP v, eq_12 1 blocksP v] at hP
  have hsplit : moment t (Pprime blocksP targetsT v J B) =
      moment t (splitBlocks J (tpow blocksP v)) +
        moment t (splitBlocks J (completionBlocks B (tpow targetsT v))) := by
    simp [Pprime, splitBlocks, Multiset.add_bind, moment]
  have hcard := completionBlocks_card_le B (tpow targetsT v)
  have hc' : Multiset.card (completionBlocks B (tpow targetsT v)) ≤
      Multiset.card targetsT ^ v :=
    hcard.trans (le_of_eq (card_tpow targetsT v))
  have hc : (Multiset.card (completionBlocks B (tpow targetsT v)) : ℝ) ≤
      (Multiset.card targetsT : ℝ) ^ v := by
    exact_mod_cast hc'
  have hone : 2 * (Multiset.card (completionBlocks B (tpow targetsT v)) : ℝ) *
        (B : ℝ) * (J : ℝ) ^ (t - 1) ≤
      2 * (Multiset.card targetsT : ℝ) ^ v * (B : ℝ) * (J : ℝ) ^ (t - 1) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2)) (Nat.cast_nonneg B))
      (Real.rpow_nonneg (Nat.cast_nonneg J) _)
  constructor
  · rw [hsplit]
    exact (add_le_add hP hQ).trans (add_le_add_right hone _)
  · change moment t targetsT ^ v ≤ moment t (completeTargets B (tpow targetsT v))
    rw [← eq_12 t targetsT v]
    exact completeTargets_moment_ge t ht0 B (tpow targetsT v)
