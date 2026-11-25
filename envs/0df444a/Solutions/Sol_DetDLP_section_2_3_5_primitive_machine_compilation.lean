-- Prove2me | solution 1 for DetDLP.section_2_3_5_primitive_machine_compilation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T14:40:16.107797+00:00
-- url     : https://prove2.me/submissions/1292b192-3cf9-4707-9c34-4dc16cabf0a1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DetDLP_BTN
import Definitions.Def_DetDLP_FactorBase
import Theorems.Thm_DetDLP_milestones_8_9_primitive_machine_compilation

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open DetDLP

/-- Reduction of `DetDLP.section_2_3_5_primitive_machine_compilation` to
`DetDLP.milestones_8_9_primitive_machine_compilation`. -/
theorem solution :
    ((∀ (M : PrimitiveMachine) (input : List Bool) (k : ℕ) (c : LocatedCfg M),
        Trace (locatedStep M) k (locatedInit M input) c →
        visitedSpace c ≤ input.length + M.tapeCount + k) →
      ((∀ (nV M Δ : ℕ) (deg : Fin nV → ℕ),
          1 ≤ Δ → (∑ v : Fin nV, deg v) ≤ 2 * M →
          Δ * (Finset.univ.filter (fun v : Fin nV => Δ ≤ deg v)).card ≤ 2 * M ∧
          (Finset.univ.filter (fun v : Fin nV => Δ ≤ deg v)).card ≤ 2 * M / Δ) ∧
       (∀ (P e : ℕ) (x y : ℤ),
          ((2 : ℤ) ^ e * x ≡ (2 : ℤ) ^ e * y [ZMOD (2 : ℤ) ^ (P + e)]) ↔
            (x ≡ y [ZMOD (2 : ℤ) ^ P])) ∧
       (∀ (P e c d : ℕ), c < 2 ^ P → d < 2 ^ P →
          ((2 : ℤ) ^ e * (c : ℤ) ≡ (2 : ℤ) ^ e * (d : ℤ) [ZMOD (2 : ℤ) ^ (P + e)]) →
          c = d)) →
      (∀ (C c0 : ℕ), 0 < C → 0 < c0 →
        ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
          ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
            ∀ (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
              (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P ℓ'),
              2 ≤ β →
              1 ≤ Told →
              G.nE ≤ C * β →
              G.nV ≤ β ^ c0 →
              1 ≤ P → P ≤ C * β →
              1 ≤ ℓ' → ℓ' ≤ C * β →
              BTNEntryEvaluable desc G P ℓ' T E outE (Told : ℝ) (((β + desc.length : ℕ) : ℝ) ^ c0) →
              let Δbar : ℕ := max G.maxDeg (Nat.ceil ((β : ℝ) ^ ((9 : ℝ) / 10)))
              let ρ : ℕ := max 1 (Nat.floor (Real.logb 2 ((β : ℝ) / (Δbar : ℝ))))
              ∃ w : List Bool,
                EncodesTruncPoly P ℓ' w (BTNContract G T) ∧
                RunsWithin M outM (encodeBTNInstance desc G β P ℓ') w
                  (polyBound K (β + desc.length) * (Told : ℝ) *
                    (2 : ℝ) ^ ((K : ℝ) * (β : ℝ) / Real.sqrt (ρ : ℝ)))
                  (polyBound K (β + desc.length))) ∧
      (∃ (E : PrimitiveMachine) (outE : Fin E.tapeCount) (K : ℕ),
        ∀ d : ℕ, 1 ≤ d →
          ∃ (G : BipartiteMultigraph)
            (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
            (ext : Fin (4 * d) → Fin G.nE),
            G.nE < 1100 * (d + 1) ∧
            (G.maxDeg : ℝ) < 136 * ((d : ℝ) + 1) ^ ((3 : ℝ) / 4) ∧
            (G.nV : ℝ) ≤ polyBound K d ∧
            BoolBTNEntryEvaluable (countWord d) G T E outE (polyBound K d) (polyBound K d) ∧
            IsParsimonious G T ext (fun x =>
              bitsToNat (fun i : Fin d => x ⟨i.val, by omega⟩) *
              bitsToNat (fun i : Fin d => x ⟨d + i.val, by omega⟩) =
              bitsToNat (fun i : Fin (2 * d) => x ⟨2 * d + i.val, by omega⟩))) ∧
      ((∀ (C A c0 : ℕ), 0 < C → 0 < A → 0 < c0 →
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
        (∃ (M_enum : PrimitiveMachine) (out_enum : Fin M_enum.tapeCount)
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
                ((¬(64 ≤ gord ∧ 4096 * m ≤ n) ∧ ∀ i : Fin m, (F i).toFinset = Finset.univ) ∨
                  (64 ≤ gord ∧ 4096 * m ≤ n ∧
                    ∃ S : ECSeed p m,
                      (∀ i : Fin m, (F i).toFinset = ecFactorBlock E (hashThreshold p n m gord) S i) ∧
                      collisionPotentialAdd ((qBlk p n (hashThreshold p n m gord)) ^ m)
                        (ecFactorBlock E (hashThreshold p n m gord) S) ≤
                        (∑ S' : ECSeed p m,
                          collisionPotentialAdd ((qBlk p n (hashThreshold p n m gord)) ^ m)
                            (ecFactorBlock E (hashThreshold p n m gord) S')) /
                          (Fintype.card (ECSeed p m) : ℝ))) ∧
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
                      (mainSpaceBound C b) (polyBound C b)) ∧
        (∃ (M_enum : PrimitiveMachine) (out_enum : Fin M_enum.tapeCount)
           (M_dec : PrimitiveMachine) (out_dec : Fin M_dec.tapeCount) (C : ℕ),
          ∀ (p : ℕ) [Fact p.Prime],
            let b := bitLen p
            let m := blockCount b
            let gord := p - 1
            let n := p - 1
            ∃ F : Fin m → List (ZMod p)ˣ,
              (∀ i : Fin m, (F i).Nodup) ∧
              ((¬(64 ≤ gord ∧ 4096 * m ≤ n) ∧ ∀ i : Fin m, (F i).toFinset = Finset.univ) ∨
                (64 ≤ gord ∧ 4096 * m ≤ n ∧
                  ∃ S : FpSeed p m,
                    (∀ i : Fin m, (F i).toFinset = fpFactorBlock (p := p) (hashThreshold p n m gord) S i) ∧
                    collisionPotentialMul ((qBlk p n (hashThreshold p n m gord)) ^ m)
                      (fpFactorBlock (p := p) (hashThreshold p n m gord) S) ≤
                      (∑ S' : FpSeed p m,
                        collisionPotentialMul ((qBlk p n (hashThreshold p n m gord)) ^ m)
                          (fpFactorBlock (p := p) (hashThreshold p n m gord) S')) /
                        (Fintype.card (FpSeed p m) : ℝ))) ∧
              RunsWithin M_enum out_enum (countWord p) (encodeFpFactorBlocks F)
                (mainSpaceBound C b) (mainSpaceBound C b) ∧
              ∀ X : (ZMod p)ˣ,
                (∃ A B : Fin m → (ZMod p)ˣ,
                  (∀ i : Fin m, A i ∈ F i ∧ B i ∈ F i) ∧
                  (∏ i : Fin m, (A i * B i)) = X) →
                ∃ A B : Fin m → (ZMod p)ˣ,
                  (∀ i : Fin m, A i ∈ F i ∧ B i ∈ F i) ∧
                  (∏ i : Fin m, (A i * B i)) = X ∧
                  RunsWithin M_dec out_dec
                    (encodeNatListBin [p, (X : ZMod p).val])
                    (encodeFpDecomp A B)
                    (mainSpaceBound C b) (polyBound C b))) ∧
      (((∀ (C A c0 : ℕ), 0 < C → 0 < A → 0 < c0 →
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
        (∃ (E : PrimitiveMachine) (outE : Fin E.tapeCount) (K : ℕ),
          ∀ d : ℕ, 1 ≤ d →
            ∃ (G : BipartiteMultigraph)
              (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
              (ext : Fin (4 * d) → Fin G.nE),
              G.nE < 1100 * (d + 1) ∧
              (G.maxDeg : ℝ) < 136 * ((d : ℝ) + 1) ^ ((3 : ℝ) / 4) ∧
              (G.nV : ℝ) ≤ polyBound K d ∧
              BoolBTNEntryEvaluable (countWord d) G T E outE (polyBound K d) (polyBound K d) ∧
              IsParsimonious G T ext (fun x =>
                bitsToNat (fun i : Fin d => x ⟨i.val, by omega⟩) *
                bitsToNat (fun i : Fin d => x ⟨d + i.val, by omega⟩) =
                bitsToNat (fun i : Fin (2 * d) => x ⟨2 * d + i.val, by omega⟩))) →
        ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
          ∀ N : ℕ, 2 ≤ N →
            let n := bitLen (N + 1)
            RunsWithin M out (countWord N) (countWord N.minFac)
              ((2 : ℝ) ^ ((K : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ)))) (polyBound K n)) ∧
       (∀ (f : ℕ → ℕ) (Md : PrimitiveMachine) (od : Fin Md.tapeCount) (Kd : ℕ),
        (∀ N : ℕ, 2 ≤ N →
          let n := bitLen (N + 1)
          RunsWithin Md od (countWord N) (countWord (f N))
            ((2 : ℝ) ^ ((Kd : ℝ) * n / Real.sqrt (logSafe n))) (polyBound Kd n)) →
        ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
          ∀ N : ℕ, 2 ≤ N →
            let n := bitLen (N + 1)
            let split : ℕ → ℕ → List ℕ :=
              Nat.rec (motive := fun _ => ℕ → List ℕ) (fun x => [x]) (fun _ prev x =>
                let d := f x
                if 2 ≤ d ∧ d < x ∧ d ∣ x then prev d ++ prev (x / d) else [x])
            RunsWithin M out (countWord N) (encodeNatListBin ((split n N).mergeSort))
              ((2 : ℝ) ^ ((K : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ)))) (polyBound K n)) ∧
       (∀ (Mf : PrimitiveMachine) (ofac : Fin Mf.tapeCount) (Kf : ℕ),
        (∀ N : ℕ, 2 ≤ N →
          let n := bitLen (N + 1)
          RunsWithin Mf ofac (countWord N) (encodeNatListBin N.primeFactorsList)
            ((2 : ℝ) ^ ((Kf : ℝ) * n / Real.sqrt (logSafe n))) (polyBound Kf n)) →
        ∀ (Me : PrimitiveMachine) (oe : Fin Me.tapeCount) (Ke : ℕ),
          ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (C : ℕ),
            ∀ (p : ℕ) [Fact p.Prime],
              let b := bitLen p
              let m := blockCount b
              ∀ F : Fin m → List (ZMod p)ˣ,
                RunsWithin Me oe (countWord p) (encodeFpFactorBlocks F)
                  (mainSpaceBound Ke b) (mainSpaceBound Ke b) →
                let n := p - 1
                let U := (List.ofFn F).flatten
                let h : (ZMod p)ˣ := ∏ r ∈ n.primeFactors,
                  ((U.find? (fun u => decide (u ^ (n / r) ≠ 1))).getD 1) ^ (n / r ^ (n.factorization r))
                RunsWithin M out (countWord p) (countWord (h : ZMod p).val)
                  (mainSpaceBound C b) (mainSpaceBound C b)))) := by
  intro _htrace
  exact milestones_8_9_primitive_machine_compilation
