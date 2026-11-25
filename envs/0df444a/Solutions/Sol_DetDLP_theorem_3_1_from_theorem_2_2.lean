-- Prove2me | solution 1 for DetDLP.theorem_3_1_from_theorem_2_2
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T09:47:19.808382+00:00
-- url     : https://prove2.me/submissions/db5a697a-7848-4a8a-be27-6106ad4d548d

import Mathlib
import Definitions.Def_DetDLP_BTN
import Definitions.Def_DetDLP_FactorBase
import Theorems.Thm_DetDLP_lemma_3_2_collision_potential
import Theorems.Thm_DetDLP_dense_covering_and_2m_decomp
import Theorems.Thm_DetDLP_ec_stage1_tm_from_seed_witness
import Theorems.Thm_DetDLP_fp_stage1_tm_from_seed_witness

set_option autoImplicit false

open DetDLP
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private lemma exists_le_of_avg_le {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (B : ℝ) (havg : (∑ x : α, f x) / (Fintype.card α : ℝ) ≤ B) :
    ∃ x : α, f x ≤ B := by
  have hpos : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos (α := α)
  have hsum : ∑ x : α, f x ≤ ∑ _x : α, B := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    exact (div_le_iff₀ hpos).mp havg
  obtain ⟨x, _, hx⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨x, hx⟩

private lemma qBlk_pow_pos {p n m gord : ℕ} (hp : 2 ≤ p) (hm : 2 ≤ m)
    (hn : 4096 * m ≤ n) :
    0 < (qBlk p n (hashThreshold p n m gord)) ^ m := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hqstar_pos : 0 < qStar m gord := by
    have : 4096 * m ≤ qStar m gord := le_max_left _ _
    omega
  have hT_pos : 1 ≤ hashThreshold p n m gord := by
    unfold hashThreshold
    have hq_pos : (0 : ℝ) < (qStar m gord : ℝ) := by exact_mod_cast hqstar_pos
    exact Nat.succ_le_of_lt (Nat.ceil_pos.mpr (by positivity))
  have hT_posR : (0 : ℝ) < (hashThreshold p n m gord : ℝ) := by exact_mod_cast (by omega : 0 < hashThreshold p n m gord)
  have hq_pos : 0 < qBlk p n (hashThreshold p n m gord) := by
    unfold qBlk; positivity
  exact pow_pos hq_pos m

private lemma blockCount_ge_two (b : ℕ) : 2 ≤ blockCount b :=
  le_max_left 2 _

theorem solution (h22 :
    ∀ (C A c0 : ℕ), 0 < C → 0 < A → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (s P0 ℓ : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P0 ℓ),
            2 ≤ s →
            G.nE ≤ C * s →
            G.nV ≤ s ^ c0 →
            G.maxDeg ≤ Nat.ceil ((s : ℝ) ^ ((9 : ℝ) / 10)) →
            1 ≤ P0 → P0 ≤ C * s →
            1 ≤ ℓ → ℓ ≤ C * s →
            BTNEntryEvaluable desc G P0 ℓ T E outE
              (((s + desc.length : ℕ) : ℝ) ^ c0 * (2 : ℝ) ^ ((A : ℝ) * (s : ℝ) ^ ((9 : ℝ) / 10)))
              (((s + desc.length : ℕ) : ℝ) ^ c0) →
            ∃ w : List Bool,
              EncodesTruncPoly P0 ℓ w (BTNContract G T) ∧
              RunsWithin M outM (encodeBTNInstance desc G s P0 ℓ) w
                (btnTimeBound K (s + desc.length) s)
                (polyBound K (s + desc.length))) :
    (∃ (M_enum : PrimitiveMachine) (out_enum : Fin M_enum.tapeCount)
       (M_dec : PrimitiveMachine) (out_dec : Fin M_dec.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime], 3 < p →
        ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
          letI := ecPointFintype E
          let b := bitLen p
          let m := blockCount b
          let gord := Fintype.card E.toAffine.Point
          ∃ F : Fin m → List E.toAffine.Point,
            (∀ i : Fin m, (F i).Nodup) ∧
            ((∑ i : Fin m, (F i).length : ℕ) : ℝ) ≤
              (C : ℝ) * ((m : ℝ) ^ 2 + (m : ℝ) * (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ))) ∧
            7 * gord ≤ 8 * (sumsetAdd (fun i => (F i).toFinset)).card ∧
            RunsWithin M_enum out_enum (encodeCurveInput p E) (encodeECFactorBlocks F)
              (mainSpaceBound C b) (mainSpaceBound C b) ∧
            ∀ X : E.toAffine.Point,
              ∃ A B : Fin m → E.toAffine.Point,
                (∀ i : Fin m, A i ∈ F i ∧ B i ∈ F i) ∧
                (∑ i : Fin m, (A i + B i)) = X ∧
                RunsWithin M_dec out_dec
                  (Encoding.encodeList id [encodeCurveInput p E, encodeNatListBin (pointCoords X)])
                  (encodeECDecomp A B)
                  (mainSpaceBound C b) (polyBound C b)) ∧
    (∃ (M_enum : PrimitiveMachine) (out_enum : Fin M_enum.tapeCount)
       (M_dec : PrimitiveMachine) (out_dec : Fin M_dec.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime],
        let b := bitLen p
        let m := blockCount b
        let gord := p - 1
        ∃ F : Fin m → List (ZMod p)ˣ,
          (∀ i : Fin m, (F i).Nodup) ∧
          ((∑ i : Fin m, (F i).length : ℕ) : ℝ) ≤
            (C : ℝ) * ((m : ℝ) ^ 2 + (m : ℝ) * (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ))) ∧
          7 * gord ≤ 8 * (prodsetMul (fun i => (F i).toFinset)).card ∧
          RunsWithin M_enum out_enum (countWord p) (encodeFpFactorBlocks F)
            (mainSpaceBound C b) (mainSpaceBound C b) ∧
          ∀ X : (ZMod p)ˣ,
            ∃ A B : Fin m → (ZMod p)ˣ,
              (∀ i : Fin m, A i ∈ F i ∧ B i ∈ F i) ∧
              (∏ i : Fin m, (A i * B i)) = X ∧
              RunsWithin M_dec out_dec
                (encodeNatListBin [p, (X : ZMod p).val])
                (encodeFpDecomp A B)
                (mainSpaceBound C b) (polyBound C b)) := by
  constructor
  · -- Part 1: Elliptic-curve case
    have hseed_ec :
        ∀ (p m : ℕ) [Fact p.Prime], 3 < p → 2 ≤ m →
          ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
            letI := ecPointFintype E
            let gord := Fintype.card E.toAffine.Point
            let n := gord - 1
            64 ≤ gord → 4096 * m ≤ n →
            let T := hashThreshold p n m gord
            let μ := (qBlk p n T) ^ m
            ∃ S : ECSeed p m, collisionPotentialAdd μ (ecFactorBlock E T S) ≤ (373 : ℝ) / 336 := by
      intro p m _ hp3 hm E _
      let _ := ecPointFintype E
      dsimp only
      intro hg64 hn4096
      have : Nonempty (ECSeed p m) := ⟨fun _ _ => (⟨0, by omega⟩, ⟨0, by omega⟩)⟩
      exact exists_le_of_avg_le _ _ (DetDLP.lemma_3_2_collision_potential.1 p m hp3 hm E hg64 hn4096)
    obtain ⟨M_enum, out_enum, M_dec, out_dec, C, hTM⟩ :=
      DetDLP.ec_stage1_tm_from_seed_witness h22 hseed_ec
    refine ⟨M_enum, out_enum, M_dec, out_dec, C, ?_⟩
    intro p _ hp3 E _
    let _ := ecPointFintype E
    dsimp only
    obtain ⟨F, hnodup, hsize, hregime, hrun_enum, hrun_dec⟩ := hTM p hp3 E
    have hm2 : 2 ≤ blockCount (bitLen p) := blockCount_ge_two _
    have hcov_and_dec :
        7 * Fintype.card E.toAffine.Point ≤
          8 * (sumsetAdd (fun i => (F i).toFinset)).card ∧
        ∀ X : E.toAffine.Point,
          ∃ A B : Fin (blockCount (bitLen p)) → E.toAffine.Point,
            (∀ i, A i ∈ F i ∧ B i ∈ F i) ∧
            (∑ i, (A i + B i)) = X := by
      rcases hregime with hsmall | ⟨hg64, hn4096, S, hF_eq, hΦ⟩
      · -- Small-group regime: F_i = E(F_p)
        have hsumset_univ : sumsetAdd (fun i => (F i).toFinset) = Finset.univ := by
          ext X
          simp only [Finset.mem_univ, iff_true, sumsetAdd, Finset.mem_image, Fintype.mem_piFinset]
          let i0 : Fin (blockCount (bitLen p)) := ⟨0, by omega⟩
          refine ⟨fun i => if i = i0 then X else 0, fun i => by rw [hsmall i]; exact Finset.mem_univ _, ?_⟩
          simp
        refine ⟨by rw [hsumset_univ, Finset.card_univ]; omega, fun X => ?_⟩
        let i0 : Fin (blockCount (bitLen p)) := ⟨0, by omega⟩
        refine ⟨fun i => if i = i0 then X else 0, fun _ => 0, fun i => ?_, ?_⟩
        · have hmem : ∀ P : E.toAffine.Point, P ∈ F i := fun P => by
            rw [← List.mem_toFinset, hsmall i]; exact Finset.mem_univ P
          exact ⟨hmem _, hmem _⟩
        · simp
      · -- General regime: apply Cauchy-Schwarz covering & 2m-decomposition
        have hμ_pos := qBlk_pow_pos (p := p) (n := Fintype.card E.toAffine.Point - 1)
          (m := blockCount (bitLen p)) (gord := Fintype.card E.toAffine.Point)
          (by omega) hm2 hn4096
        have hΦ_lt : collisionPotentialAdd
            (qBlk p (Fintype.card E.toAffine.Point - 1)
              (hashThreshold p (Fintype.card E.toAffine.Point - 1) (blockCount (bitLen p))
                (Fintype.card E.toAffine.Point)) ^ blockCount (bitLen p))
            (ecFactorBlock E (hashThreshold p (Fintype.card E.toAffine.Point - 1)
              (blockCount (bitLen p)) (Fintype.card E.toAffine.Point)) S) < (64 : ℝ) / 57 := by
          linarith
        obtain ⟨h78, hdec⟩ := DetDLP.dense_covering_and_2m_decomp.1 _ _ hμ_pos hΦ_lt
        have hfun_eq : (fun i => (F i).toFinset) =
            ecFactorBlock E (hashThreshold p (Fintype.card E.toAffine.Point - 1)
              (blockCount (bitLen p)) (Fintype.card E.toAffine.Point)) S :=
          funext hF_eq
        refine ⟨by rw [hfun_eq]; exact h78, fun X => ?_⟩
        obtain ⟨A, B, hAB, hsum⟩ := hdec X
        refine ⟨A, B, fun i => ?_, hsum⟩
        have h1 := (hAB i).1
        have h2 := (hAB i).2
        rw [← hF_eq i, List.mem_toFinset] at h1 h2
        exact ⟨h1, h2⟩
    exact ⟨F, hnodup, hsize, hcov_and_dec.1, hrun_enum, fun X => hrun_dec X (hcov_and_dec.2 X)⟩
  · -- Part 2: Multiplicative F_p^* case
    have hseed_fp :
        ∀ (p m : ℕ) [Fact p.Prime], 2 ≤ m →
          let gord := p - 1
          let n := p - 1
          64 ≤ gord → 4096 * m ≤ n →
          let T := hashThreshold p n m gord
          let μ := (qBlk p n T) ^ m
          ∃ S : FpSeed p m, collisionPotentialMul μ (fpFactorBlock (p := p) T S) ≤ (373 : ℝ) / 336 := by
      intro p m _ hm
      dsimp only
      intro hg64 hn4096
      have hp : p.Prime := Fact.out
      have : Nonempty (FpSeed p m) := ⟨fun _ => (⟨0, by omega⟩, ⟨0, hp.pos⟩)⟩
      exact exists_le_of_avg_le _ _ (DetDLP.lemma_3_2_collision_potential.2 p m hm hg64 hn4096)
    obtain ⟨M_enum, out_enum, M_dec, out_dec, C, hTM⟩ :=
      DetDLP.fp_stage1_tm_from_seed_witness h22 hseed_fp
    refine ⟨M_enum, out_enum, M_dec, out_dec, C, ?_⟩
    intro p _
    dsimp only
    have hp : p.Prime := Fact.out
    obtain ⟨F, hnodup, hsize, hregime, hrun_enum, hrun_dec⟩ := hTM p
    have hm2 : 2 ≤ blockCount (bitLen p) := blockCount_ge_two _
    have hcard_u : Fintype.card (ZMod p)ˣ = p - 1 := ZMod.card_units p
    have hcov_and_dec :
        7 * (p - 1) ≤ 8 * (prodsetMul (fun i => (F i).toFinset)).card ∧
        ∀ X : (ZMod p)ˣ,
          ∃ A B : Fin (blockCount (bitLen p)) → (ZMod p)ˣ,
            (∀ i, A i ∈ F i ∧ B i ∈ F i) ∧
            (∏ i, (A i * B i)) = X := by
      rcases hregime with hsmall | ⟨hg64, hn4096, S, hF_eq, hΦ⟩
      · have hprodset_univ : prodsetMul (fun i => (F i).toFinset) = Finset.univ := by
          ext X
          simp only [Finset.mem_univ, iff_true, prodsetMul, Finset.mem_image, Fintype.mem_piFinset]
          let i0 : Fin (blockCount (bitLen p)) := ⟨0, by omega⟩
          refine ⟨fun i => if i = i0 then X else 1, fun i => by rw [hsmall i]; exact Finset.mem_univ _, ?_⟩
          simp
        refine ⟨by rw [hprodset_univ, Finset.card_univ, hcard_u]; omega, fun X => ?_⟩
        let i0 : Fin (blockCount (bitLen p)) := ⟨0, by omega⟩
        refine ⟨fun i => if i = i0 then X else 1, fun _ => 1, fun i => ?_, ?_⟩
        · have hmem : ∀ a : (ZMod p)ˣ, a ∈ F i := fun a => by
            rw [← List.mem_toFinset, hsmall i]; exact Finset.mem_univ a
          exact ⟨hmem _, hmem _⟩
        · simp
      · have hμ_pos := qBlk_pow_pos (p := p) (n := p - 1)
          (m := blockCount (bitLen p)) (gord := p - 1) hp.two_le hm2 hn4096
        have hΦ_lt : collisionPotentialMul
            (qBlk p (p - 1) (hashThreshold p (p - 1) (blockCount (bitLen p)) (p - 1)) ^
              blockCount (bitLen p))
            (fpFactorBlock (p := p) (hashThreshold p (p - 1) (blockCount (bitLen p)) (p - 1)) S) <
            (64 : ℝ) / 57 := by
          linarith
        obtain ⟨h78, hdec⟩ := DetDLP.dense_covering_and_2m_decomp.2 _ _ hμ_pos hΦ_lt
        rw [hcard_u] at h78
        have hfun_eq : (fun i => (F i).toFinset) =
            fpFactorBlock (p := p) (hashThreshold p (p - 1) (blockCount (bitLen p)) (p - 1)) S :=
          funext hF_eq
        refine ⟨by rw [hfun_eq]; exact h78, fun X => ?_⟩
        obtain ⟨A, B, hAB, hprod⟩ := hdec X
        refine ⟨A, B, fun i => ?_, hprod⟩
        have h1 := (hAB i).1
        have h2 := (hAB i).2
        rw [← hF_eq i, List.mem_toFinset] at h1 h2
        exact ⟨h1, h2⟩
    exact ⟨F, hnodup, hsize, hcov_and_dec.1, hrun_enum, fun X => hrun_dec X (hcov_and_dec.2 X)⟩
