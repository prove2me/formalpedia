-- Prove2me | solution 1 for DetDLP.fp_primitive_root_tm_from_oracles
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T11:53:00.261807+00:00
-- url     : https://prove2.me/submissions/6944ccf5-e2ca-45a1-8c90-08d65a1140c4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DetDLP_FactorBase
import Theorems.Thm_DetDLP_primitive_root_scan_correctness
import Theorems.Thm_DetDLP_stage1_complexity_dominance
import Theorems.Thm_DetDLP_fp_primitive_root_scan_tm_compile

set_option autoImplicit false

open DetDLP
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private lemma runsWithin_mono {A : PrimitiveMachine} {out : Fin A.tapeCount}
    {input output : List Bool} {τ₁ τ₂ σ₁ σ₂ : ℝ}
    (h : RunsWithin A out input output τ₁ σ₁) (hτ : τ₁ ≤ τ₂) (hσ : σ₁ ≤ σ₂) :
    RunsWithin A out input output τ₂ σ₂ := by
  obtain ⟨time, final, htr, hst, hout, htime, hspace⟩ := h
  exact ⟨time, final, htr, hst, hout, le_trans htime hτ,
    fun k c hk htk => le_trans (hspace k c hk htk) hσ⟩

theorem solution :
    (∃ (M_fac : PrimitiveMachine) (out_fac : Fin M_fac.tapeCount) (K : ℕ),
      ∀ N : ℕ, 2 ≤ N →
        let n := bitLen (N + 1)
        RunsWithin M_fac out_fac (countWord N) (encodeNatListBin N.primeFactorsList)
          ((2 : ℝ) ^ ((K : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ))))
          (polyBound K n)) →
    (∃ (M_enum : PrimitiveMachine) (out_enum : Fin M_enum.tapeCount) (C_fb : ℕ),
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
          (∀ π ∈ (p - 1).primeFactors, ∃ i : Fin m, ∃ u ∈ F i, u ^ ((p - 1) / π) ≠ 1)) →
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime],
        ∃ a : ℕ → (ZMod p)ˣ,
          (∀ π ∈ (p - 1).primeFactors, (a π) ^ ((p - 1) / π) ≠ 1) ∧
          let h := ∏ π ∈ (p - 1).primeFactors,
            (a π) ^ ((p - 1) / π ^ (p - 1).factorization π)
          RunsWithin M out (countWord p) (countWord (h : ZMod p).val)
            (mainSpaceBound C (bitLen p)) (mainSpaceBound C (bitLen p)) := by
  intro hfac hfb
  obtain ⟨M_fac, out_fac, K, hM_fac⟩ := hfac
  obtain ⟨C_poly, hC_poly⟩ := DetDLP.stage1_complexity_dominance.2.2.1 K 0
  have hfac_msb :
      ∃ (M_fac : PrimitiveMachine) (out_fac : Fin M_fac.tapeCount) (K_fac : ℕ),
        ∀ N : ℕ, 2 ≤ N →
          let n := bitLen (N + 1)
          RunsWithin M_fac out_fac (countWord N) (encodeNatListBin N.primeFactorsList)
            (mainSpaceBound K_fac n) (mainSpaceBound K_fac n) := by
    let K_fac := max K C_poly
    refine ⟨M_fac, out_fac, K_fac, fun N hN => ?_⟩
    dsimp only
    have htime1 := DetDLP.stage1_complexity_dominance.2.1 K (bitLen (N + 1))
    have htime2 := (DetDLP.stage1_complexity_dominance.1 K K_fac (bitLen (N + 1)) (le_max_left _ _)).1
    have hspace1 := (hC_poly (N + 1) 0 (by omega) (by omega)).1
    have hspace2 := (DetDLP.stage1_complexity_dominance.1 C_poly K_fac (bitLen (N + 1)) (le_max_right _ _)).1
    exact runsWithin_mono (hM_fac N hN) (le_trans htime1 htime2) (le_trans hspace1 hspace2)
  obtain ⟨M_enum, out_enum, C_fb, hM_enum⟩ := hfb
  obtain ⟨C_sz, hC_sz⟩ := DetDLP.stage1_complexity_dominance.2.2.1 1 C_fb
  have hfb_msb :
      ∃ (M_enum : PrimitiveMachine) (out_enum : Fin M_enum.tapeCount) (C_fb' : ℕ),
        ∀ (p : ℕ) [Fact p.Prime],
          let b := bitLen p
          let m := blockCount b
          ∃ F : Fin m → List (ZMod p)ˣ,
            (∀ i : Fin m, (F i).Nodup) ∧
            ((∑ i : Fin m, (F i).length : ℕ) : ℝ) ≤ mainSpaceBound C_fb' b ∧
            RunsWithin M_enum out_enum (countWord p) (encodeFpFactorBlocks F)
              (mainSpaceBound C_fb' b) (mainSpaceBound C_fb' b) ∧
            (∀ π ∈ (p - 1).primeFactors, ∃ i : Fin m, ∃ u ∈ F i, u ^ ((p - 1) / π) ≠ 1) := by
    let C_fb' := max C_fb C_sz
    refine ⟨M_enum, out_enum, C_fb', fun p _ => ?_⟩
    dsimp only
    have hp : p.Prime := Fact.out
    obtain ⟨F, hnodup, hsize, hrun, hwit⟩ := hM_enum p
    have hpoly1 : (1 : ℝ) ≤ polyBound 1 (bitLen p) := by
      simp only [polyBound, Nat.cast_one, one_mul, pow_one]
      linarith [Nat.cast_nonneg (α := ℝ) (bitLen p)]
    have hsz1 := (hC_sz p (p - 1) hp.two_le (by omega)).2
    have hnn : 0 ≤ (C_fb : ℝ) * ((blockCount (bitLen p) : ℝ) ^ 2 +
        (blockCount (bitLen p) : ℝ) * ((p - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / (blockCount (bitLen p) : ℝ))) := by
      positivity
    have hsize_csz : ((∑ i : Fin (blockCount (bitLen p)), (F i).length : ℕ) : ℝ) ≤
        mainSpaceBound C_sz (bitLen p) := by
      calc ((∑ i : Fin (blockCount (bitLen p)), (F i).length : ℕ) : ℝ)
          ≤ 1 * ((C_fb : ℝ) * ((blockCount (bitLen p) : ℝ) ^ 2 +
              (blockCount (bitLen p) : ℝ) *
                ((p - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / (blockCount (bitLen p) : ℝ)))) := by
            linarith
        _ ≤ polyBound 1 (bitLen p) * _ := mul_le_mul_of_nonneg_right hpoly1 hnn
        _ ≤ mainSpaceBound C_sz (bitLen p) := hsz1
    have hmono_sz := (DetDLP.stage1_complexity_dominance.1 C_sz C_fb' (bitLen p) (le_max_right _ _)).1
    have hmono_run := (DetDLP.stage1_complexity_dominance.1 C_fb C_fb' (bitLen p) (le_max_left _ _)).1
    exact ⟨F, hnodup, le_trans hsize_csz hmono_sz,
      runsWithin_mono hrun hmono_run hmono_run, hwit⟩
  obtain ⟨M, out, C, hTM⟩ := DetDLP.fp_primitive_root_scan_tm_compile hfac_msb hfb_msb
  refine ⟨M, out, C, fun p _ => ?_⟩
  obtain ⟨F, hwit, hrun⟩ := hTM p
  let U : List (ZMod p)ˣ := (List.ofFn F).flatten
  let a : ℕ → (ZMod p)ˣ := fun π =>
    (U.find? (fun u => decide (u ^ ((p - 1) / π) ≠ 1))).getD 1
  have ha := (DetDLP.primitive_root_scan_correctness p (blockCount (bitLen p)) F hwit).1
  exact ⟨a, ha, hrun⟩
