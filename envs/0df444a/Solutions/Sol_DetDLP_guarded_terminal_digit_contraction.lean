-- Prove2me | solution 1 for DetDLP.guarded_terminal_digit_contraction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T13:51:48.207308+00:00
-- url     : https://prove2.me/submissions/56cb5446-06bb-497b-9208-526e8d66e073
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_DetDLP_uniformly_enumerable_terminal_expansion_with_entry_machine
import Theorems.Thm_DetDLP_d4_small_regime_terminal_machine
import Theorems.Thm_DetDLP_d4_residual_digit_entry_machine
import Theorems.Thm_DetDLP_d4_outer_scalar_cursor_machine_v2
open DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open DetDLP.D4Plan

theorem solution
    (hscalar :
    ∀ (C c0 : ℕ), 0 < C → 0 < c0 →
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
                (polyBound K (β + desc.length))) :
    ∀ (C c0 : ℕ), 0 < C → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (b m k S P0 ℓ : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin ℓ → ℕ),
            2 ≤ b →
            1 ≤ m → 1 ≤ k →
            blockCount b ≤ C * m → m ≤ C * blockCount b →
            S ≤ C * m * b →
            4 * m * k ≤ C * b → b ≤ C * (4 * m * k) →
            1 ≤ P0 → P0 ≤ S →
            1 ≤ ℓ → ℓ ≤ C * m →
            G.nV ≤ (S + desc.length + 1) ^ c0 →
            ∀ (spec : LookupSeparatorSpec G m k S (C * Nat.ceil ((b : ℝ) ^ ((3 : ℝ) / 4)))),
            (∀ v t i, A v t i < 2^P0) →
            (∀ v t, RunsWithin E outE (encodePortQuery desc v.val (List.ofFn t))
              (encodeNatListBin (List.ofFn (A v t))) (polyBound c0 (S+desc.length))
              (polyBound c0 (S+desc.length))) →
            let Z := BTNContract G (fun v t => ∑ i : Fin ℓ,
              Polynomial.monomial i.val (A v t i : ℤ))
            ∃ (guard modes : ℕ) (terms : Fin modes → Fin ℓ → ℤ),
              (∀ i, (∑ ν, terms ν i) ≡ (2:ℤ)^guard * Z.coeff i.val
                [ZMOD (2:ℤ)^(guard+P0)]) ∧
              RunsWithin M outM (encodeTerminalBTNInstance desc G b m k S P0 ℓ spec.lookupVerts)
                (encodeNatListBin (List.ofFn fun i =>
                  ((∑ ν, terms ν i : ℤ) : ZMod (2^(guard+P0))).val / 2^guard))
                (polyBound K (S+desc.length) * (2:ℝ)^((K:ℝ)*
                  ((b:ℝ)/m+(b:ℝ)/Real.sqrt (logSafe m))))
                (polyBound K (S+desc.length)) := by
  intro C c hC hc E o
  obtain ⟨A,B,oa,ob,e,k,L,supply⟩ := uniformly_enumerable_terminal_expansion_with_entry_machine hscalar C c hC hc E o
  obtain ⟨D,od,d,digits⟩ := d4_residual_digit_entry_machine C c k e B A ob oa
  obtain ⟨F,of₀,s,small⟩ := d4_small_regime_terminal_machine C c hC hc E o L
  obtain ⟨M,om,K,compute⟩ := d4_outer_scalar_cursor_machine_v2 hscalar C c hC hc E o L e s d A F D oa of₀ od small (by
    intro x hl he
    obtain ⟨P,bits,rank,values⟩ := supply x hl he
    exact ⟨P,bits,rank,digits P rank values⟩)
  refine ⟨M,om,K,?_⟩
  intro b m k S p l desc G A hb hm hk bm mb hS hu hl hp ps ha am nv spec bounded ev Z
  let x : Input C c := ⟨b,m,k,S,p,l,desc,G,spec,A,hb,hm,hk,bm,mb,hS,hu,hl,hp,ps,ha,am,nv,bounded⟩
  refine ⟨0,1,fun _ i => Z.coeff i.val,by simp,?_⟩
  have cast (q : ℕ) (z : ℤ) : (z : ZMod (2^(0+q))).val=(z : ZMod (2^q)).val := by rw [Nat.zero_add]
  simp only [Finset.univ_unique,Finset.sum_singleton,pow_zero,Nat.div_one]
  have eq := congrArg List.ofFn (funext fun i : Fin l => cast p (Z.coeff i.val))
  rw [eq]; exact compute x ev
