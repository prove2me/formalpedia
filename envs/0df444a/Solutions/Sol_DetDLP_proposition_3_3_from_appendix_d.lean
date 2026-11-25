-- Prove2me | solution 1 for DetDLP.proposition_3_3_from_appendix_d
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T09:06:48.414046+00:00
-- url     : https://prove2.me/submissions/7a7f241a-7c24-42d3-9de7-a0862b60d2c5

import Definitions.Def_DetDLP_OpenAIAppendixD
import Definitions.Def_DetDLP_Machine
import Definitions.Def_DetDLP_FactorBase
import Theorems.Thm_DetDLP_theorem_2_2_from_appendix_d
import Theorems.Thm_DetDLP_proposition_2_6_from_appendix_d
import Theorems.Thm_DetDLP_lemma_3_2_collision_potential
import Theorems.Thm_DetDLP_dense_covering_and_2m_decomp
import Theorems.Thm_DetDLP_fp_stage1_tm_from_seed_witness
import Theorems.Thm_DetDLP_primitive_root_from_generating_set
import Theorems.Thm_DetDLP_fp_primitive_root_tm_from_oracles

set_option autoImplicit false

open DetDLP
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private lemma exists_fp_seed_of_avg :
    ∀ (p m : ℕ) [Fact p.Prime], 2 ≤ m →
      let gord := p - 1
      let n := p - 1
      64 ≤ gord → 4096 * m ≤ n →
      let T := hashThreshold p n m gord
      let μ := (qBlk p n T) ^ m
      ∃ S : FpSeed p m, collisionPotentialMul μ (fpFactorBlock (p := p) T S) ≤ (373 : ℝ) / 336 := by
  intro p m hp hm gord n hg hn T μ
  have havg := DetDLP.lemma_3_2_collision_potential.2 p m hm hg hn
  have : Nonempty (Fin (p - 1)) := ⟨⟨0, by omega⟩⟩
  have : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
  have : Nonempty (FpSeed p m) := inferInstance
  have hcard_pos : (0 : ℝ) < (Fintype.card (FpSeed p m) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := FpSeed p m)
  have hsum : ∑ S : FpSeed p m, collisionPotentialMul μ (fpFactorBlock (p := p) T S) ≤
      ∑ _S : FpSeed p m, ((373 : ℝ) / 336) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    exact (div_le_iff₀ hcard_pos).mp havg
  obtain ⟨S, -, hS⟩ := Finset.exists_le_of_sum_le (Finset.univ_nonempty (α := FpSeed p m)) hsum
  exact ⟨S, hS⟩

private lemma qBlk_pow_pos (p m : ℕ) (hm : 2 ≤ m) (hg : 64 ≤ p - 1) :
    0 < (qBlk p (p - 1) (hashThreshold p (p - 1) m (p - 1))) ^ m := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hn_pos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < p - 1 by omega)
  have hq_pos : 0 < qStar m (p - 1) := by
    unfold qStar
    exact lt_of_lt_of_le (by omega : 0 < 4096 * m) (le_max_left _ _)
  have hT_pos : (0 : ℝ) < (hashThreshold p (p - 1) m (p - 1) : ℝ) := by
    unfold hashThreshold
    have hfrac : 0 < ((p : ℝ) * (qStar m (p - 1) : ℝ)) / ((p - 1 : ℕ) : ℝ) := by positivity
    exact_mod_cast Nat.ceil_pos.mpr hfrac
  unfold qBlk
  positivity

private lemma cover_of_stage1 {p : ℕ} [Fact p.Prime] {F : Fin (blockCount (bitLen p)) → List (ZMod p)ˣ}
    (hcase : (∀ i, (F i).toFinset = Finset.univ) ∨
      (64 ≤ p - 1 ∧ 4096 * blockCount (bitLen p) ≤ p - 1 ∧
        ∃ S : FpSeed p (blockCount (bitLen p)),
          (∀ i, (F i).toFinset = fpFactorBlock (p := p) (hashThreshold p (p - 1) (blockCount (bitLen p)) (p - 1)) S i) ∧
          collisionPotentialMul ((qBlk p (p - 1) (hashThreshold p (p - 1) (blockCount (bitLen p)) (p - 1))) ^ (blockCount (bitLen p)))
            (fpFactorBlock (p := p) (hashThreshold p (p - 1) (blockCount (bitLen p)) (p - 1)) S) ≤ (373 : ℝ) / 336)) :
    ∀ X : (ZMod p)ˣ, ∃ A B : Fin (blockCount (bitLen p)) → (ZMod p)ˣ,
      (∀ i, A i ∈ F i ∧ B i ∈ F i) ∧ (∏ i, (A i * B i)) = X := by
  have hm2 : 2 ≤ blockCount (bitLen p) := le_max_left 2 _
  rcases hcase with huniv | ⟨hg, hn, S, hFS, hpot⟩
  · intro X
    let i0 : Fin (blockCount (bitLen p)) := ⟨0, by omega⟩
    have hmem : ∀ (i : Fin (blockCount (bitLen p))) (u : (ZMod p)ˣ), u ∈ F i := by
      intro i u
      exact List.mem_toFinset.mp (by rw [huniv i]; exact Finset.mem_univ u)
    refine ⟨fun i => if i = i0 then X else 1, fun _ => 1, fun i => ⟨hmem i _, hmem i 1⟩, ?_⟩
    simp
  · intro X
    have hμ : 0 < (qBlk p (p - 1) (hashThreshold p (p - 1) (blockCount (bitLen p)) (p - 1))) ^ (blockCount (bitLen p)) :=
      qBlk_pow_pos p (blockCount (bitLen p)) hm2 hg
    have hlt : collisionPotentialMul
        ((qBlk p (p - 1) (hashThreshold p (p - 1) (blockCount (bitLen p)) (p - 1))) ^ (blockCount (bitLen p)))
        (fpFactorBlock (p := p) (hashThreshold p (p - 1) (blockCount (bitLen p)) (p - 1)) S) < (64 : ℝ) / 57 :=
      lt_of_le_of_lt hpot (by norm_num)
    obtain ⟨A, B, hAB, hprod⟩ := (DetDLP.dense_covering_and_2m_decomp.2 _ _ hμ hlt).2 X
    refine ⟨A, B, fun i => ?_, hprod⟩
    have hAi : A i ∈ (F i).toFinset := by rw [hFS i]; exact (hAB i).1
    have hBi : B i ∈ (F i).toFinset := by rw [hFS i]; exact (hAB i).2
    exact ⟨List.mem_toFinset.mp hAi, List.mem_toFinset.mp hBi⟩

theorem solution (hOAI : OpenAIAppendixDPremise) :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime],
        ∃ h : (ZMod p)ˣ,
          orderOf h = p - 1 ∧
          RunsWithin M out (countWord p) (countWord (h : ZMod p).val)
            (mainSpaceBound C (bitLen p)) (mainSpaceBound C (bitLen p)) := by
  obtain ⟨M_enum, out_enum, _M_dec, _out_dec, C_fb, hfb⟩ :=
    DetDLP.fp_stage1_tm_from_seed_witness (DetDLP.theorem_2_2_from_appendix_d hOAI) exists_fp_seed_of_avg
  have hfb_wit : ∃ (M_enum : PrimitiveMachine) (out_enum : Fin M_enum.tapeCount) (C_fb : ℕ),
      ∀ (p : ℕ) [Fact p.Prime],
        let b := bitLen p
        let m := blockCount b
        let gord := p - 1
        ∃ F : Fin m → List (ZMod p)ˣ,
          (∀ i : Fin m, (F i).Nodup) ∧
          ((∑ i : Fin m, (F i).length : ℕ) : ℝ) ≤
            (C_fb : ℝ) * ((m : ℝ) ^ 2 + (m : ℝ) * (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ))) ∧
          RunsWithin M_enum out_enum (countWord p) (encodeFpFactorBlocks F)
            (mainSpaceBound C_fb b) (mainSpaceBound C_fb b) ∧
          (∀ π ∈ (p - 1).primeFactors, ∃ i : Fin m, ∃ u ∈ F i, u ^ ((p - 1) / π) ≠ 1) := by
    refine ⟨M_enum, out_enum, C_fb, ?_⟩
    intro p hp
    obtain ⟨F, hnodup, hsize, hcase, hrun, _⟩ := hfb p
    have hcov := cover_of_stage1 (p := p) hcase
    exact ⟨F, hnodup, hsize, hrun, (DetDLP.primitive_root_from_generating_set p (blockCount (bitLen p)) F hcov).1⟩
  obtain ⟨M, out, C, hM⟩ :=
    DetDLP.fp_primitive_root_tm_from_oracles (DetDLP.proposition_2_6_from_appendix_d hOAI) hfb_wit
  refine ⟨M, out, C, ?_⟩
  intro p hp
  obtain ⟨F, -, -, hcase, -, _⟩ := hfb p
  have hcov := cover_of_stage1 (p := p) hcase
  obtain ⟨a, ha, hrun⟩ := hM p
  refine ⟨∏ π ∈ (p - 1).primeFactors, (a π) ^ ((p - 1) / π ^ (p - 1).factorization π), ?_, hrun⟩
  exact (DetDLP.primitive_root_from_generating_set p (blockCount (bitLen p)) F hcov).2 a ha
