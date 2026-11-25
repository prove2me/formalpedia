-- Prove2me | solution 1 for DetDLP.ec_stage1_tm_from_seed_witness
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T11:52:58.650138+00:00
-- url     : https://prove2.me/submissions/e461ca1c-4be7-45e6-95d0-7fcab50d8870

import Mathlib
import Definitions.Def_DetDLP_BTN
import Definitions.Def_DetDLP_FactorBase
import Theorems.Thm_DetDLP_stage1_cond_exp_derand_and_size_bounds
import Theorems.Thm_DetDLP_stage1_complexity_dominance
import Theorems.Thm_DetDLP_hasse_ec_point_count_bound
import Theorems.Thm_DetDLP_ec_stage1_btn_derand_tm

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
    (∀ (C A c0 : ℕ), 0 < C → 0 < A → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (s P0 ℓ : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P0 ℓ),
            2 ≤ s → G.nE ≤ C * s → G.nV ≤ s ^ c0 →
            G.maxDeg ≤ Nat.ceil ((s : ℝ) ^ ((9 : ℝ) / 10)) →
            1 ≤ P0 → P0 ≤ C * s → 1 ≤ ℓ → ℓ ≤ C * s →
            BTNEntryEvaluable desc G P0 ℓ T E outE
              (((s + desc.length : ℕ) : ℝ) ^ c0 * (2 : ℝ) ^ ((A : ℝ) * (s : ℝ) ^ ((9 : ℝ) / 10)))
              (((s + desc.length : ℕ) : ℝ) ^ c0) →
            ∃ w : List Bool,
              EncodesTruncPoly P0 ℓ w (BTNContract G T) ∧
              RunsWithin M outM (encodeBTNInstance desc G s P0 ℓ) w
                (btnTimeBound K (s + desc.length) s)
                (polyBound K (s + desc.length))) →
    (∀ (p m : ℕ) [Fact p.Prime], 3 < p → 2 ≤ m →
      ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
        letI := ecPointFintype E
        let gord := Fintype.card E.toAffine.Point
        let n := gord - 1
        64 ≤ gord → 4096 * m ≤ n →
        let T := hashThreshold p n m gord
        let μ := (qBlk p n T) ^ m
        ∃ S : ECSeed p m, collisionPotentialAdd μ (ecFactorBlock E T S) ≤ (373 : ℝ) / 336) →
    ∃ (M_enum : PrimitiveMachine) (out_enum : Fin M_enum.tapeCount)
      (M_dec : PrimitiveMachine) (out_dec : Fin M_dec.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime], 3 < p →
        ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
          letI := ecPointFintype E
          let b := bitLen p
          let m := blockCount b
          let gord := Fintype.card E.toAffine.Point
          let n := gord - 1
          ∃ F : Fin m → List E.toAffine.Point,
            (∀ i : Fin m, (F i).Nodup) ∧
            ((∑ i : Fin m, (F i).length : ℕ) : ℝ) ≤
              (C : ℝ) * ((m : ℝ) ^ 2 + (m : ℝ) * (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ))) ∧
            ((∀ i : Fin m, (F i).toFinset = Finset.univ) ∨
              (64 ≤ gord ∧ 4096 * m ≤ n ∧
                ∃ S : ECSeed p m,
                  (∀ i : Fin m, (F i).toFinset = ecFactorBlock E (hashThreshold p n m gord) S i) ∧
                  collisionPotentialAdd ((qBlk p n (hashThreshold p n m gord)) ^ m)
                    (ecFactorBlock E (hashThreshold p n m gord) S) ≤ (373 : ℝ) / 336)) ∧
            RunsWithin M_enum out_enum (encodeCurveInput p E) (encodeECFactorBlocks F)
              (mainSpaceBound C b) (mainSpaceBound C b) ∧
            ∀ X : E.toAffine.Point,
              (∃ A B : Fin m → E.toAffine.Point,
                (∀ i : Fin m, A i ∈ F i ∧ B i ∈ F i) ∧
                (∑ i : Fin m, (A i + B i)) = X) →
              ∃ A B : Fin m → E.toAffine.Point,
                (∀ i : Fin m, A i ∈ F i ∧ B i ∈ F i) ∧
                (∑ i : Fin m, (A i + B i)) = X ∧
                RunsWithin M_dec out_dec
                  (Encoding.encodeList id [encodeCurveInput p E, encodeNatListBin (pointCoords X)])
                  (encodeECDecomp A B)
                  (mainSpaceBound C b) (polyBound C b) := by
  intro hBTN hseed
  obtain ⟨M_enum, out_enum, M_dec, out_dec, C₀, hTM⟩ :=
    DetDLP.ec_stage1_btn_derand_tm hBTN hseed
  let C := max C₀ 32772
  refine ⟨M_enum, out_enum, M_dec, out_dec, C, fun p _ hp3 E _ => ?_⟩
  let _ := ecPointFintype E
  dsimp only
  obtain ⟨F, hnodup, hreg, hrun_enum, hrun_dec⟩ := hTM p hp3 E
  have hm2 : 2 ≤ blockCount (bitLen p) := le_max_left 2 _
  have hhasse := DetDLP.hasse_ec_point_count_bound p hp3 E
  have hreg_size :
      (¬(64 ≤ Fintype.card E.toAffine.Point ∧
          4096 * blockCount (bitLen p) ≤ Fintype.card E.toAffine.Point - 1) ∧
        ∀ i : Fin (blockCount (bitLen p)), (F i).toFinset = Finset.univ) ∨
      (64 ≤ Fintype.card E.toAffine.Point ∧
        4096 * blockCount (bitLen p) ≤ Fintype.card E.toAffine.Point - 1 ∧
        ∃ S : ECSeed p (blockCount (bitLen p)),
          ∀ i : Fin (blockCount (bitLen p)), (F i).toFinset =
            ecFactorBlock E
              (hashThreshold p (Fintype.card E.toAffine.Point - 1) (blockCount (bitLen p))
                (Fintype.card E.toAffine.Point)) S i) := by
    rcases hreg with ⟨hnot, huniv⟩ | ⟨hg, hn, S, hblk, _⟩
    · exact Or.inl ⟨hnot, huniv⟩
    · exact Or.inr ⟨hg, hn, S, hblk⟩
  have hsize_32772 :=
    DetDLP.stage1_cond_exp_derand_and_size_bounds.2.2.2.2 p (blockCount (bitLen p)) E F
      hp3 hm2 hnodup hhasse hreg_size
  have hsize : ((∑ i : Fin (blockCount (bitLen p)), (F i).length : ℕ) : ℝ) ≤
      (C : ℝ) * ((blockCount (bitLen p) : ℝ) ^ 2 +
        (blockCount (bitLen p) : ℝ) *
          (Fintype.card E.toAffine.Point : ℝ) ^ ((1 : ℝ) / (blockCount (bitLen p) : ℝ))) := by
    have hC_ge : (32772 : ℝ) ≤ (C : ℝ) := by
      have : 32772 ≤ C := le_max_right _ _
      exact_mod_cast this
    have hnn : 0 ≤ (blockCount (bitLen p) : ℝ) ^ 2 +
        (blockCount (bitLen p) : ℝ) *
          (Fintype.card E.toAffine.Point : ℝ) ^ ((1 : ℝ) / (blockCount (bitLen p) : ℝ)) := by
      positivity
    exact le_trans hsize_32772 (mul_le_mul_of_nonneg_right hC_ge hnn)
  have hreg_out :
      (∀ i : Fin (blockCount (bitLen p)), (F i).toFinset = Finset.univ) ∨
      (64 ≤ Fintype.card E.toAffine.Point ∧
        4096 * blockCount (bitLen p) ≤ Fintype.card E.toAffine.Point - 1 ∧
        ∃ S : ECSeed p (blockCount (bitLen p)),
          (∀ i : Fin (blockCount (bitLen p)), (F i).toFinset =
            ecFactorBlock E
              (hashThreshold p (Fintype.card E.toAffine.Point - 1) (blockCount (bitLen p))
                (Fintype.card E.toAffine.Point)) S i) ∧
          collisionPotentialAdd ((qBlk p (Fintype.card E.toAffine.Point - 1)
            (hashThreshold p (Fintype.card E.toAffine.Point - 1) (blockCount (bitLen p))
              (Fintype.card E.toAffine.Point))) ^ blockCount (bitLen p))
            (ecFactorBlock E
              (hashThreshold p (Fintype.card E.toAffine.Point - 1) (blockCount (bitLen p))
                (Fintype.card E.toAffine.Point)) S) ≤ (373 : ℝ) / 336) := by
    rcases hreg with ⟨_, huniv⟩ | hgen
    · exact Or.inl huniv
    · exact Or.inr hgen
  have hmono := DetDLP.stage1_complexity_dominance.1 C₀ C (bitLen p) (le_max_left _ _)
  refine ⟨F, hnodup, hsize, hreg_out, runsWithin_mono hrun_enum hmono.1 hmono.1, fun X hX => ?_⟩
  obtain ⟨A, B, hAB, hsum, hrunX⟩ := hrun_dec X hX
  exact ⟨A, B, hAB, hsum, runsWithin_mono hrunX hmono.1 hmono.2⟩
