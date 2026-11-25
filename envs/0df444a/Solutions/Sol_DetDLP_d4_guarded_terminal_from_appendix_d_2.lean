-- Prove2me | solution 2 for DetDLP.d4_guarded_terminal_from_appendix_d
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T06:49:21.098658+00:00
-- url     : https://prove2.me/submissions/f030f815-f224-4c75-8c34-35a9c4dc1d78

import Theorems.Thm_DetDLP_d4_small_regime_terminal_machine
import Theorems.Thm_DetDLP_d4_partial_unroll_rank_enumerator_v2
import Theorems.Thm_DetDLP_d4_residual_digit_entry_machine
import Theorems.Thm_DetDLP_d4_outer_scalar_cursor_machine_v2
import Theorems.Thm_DetDLP_lemma_5_2_from_appendix_d
import Definitions.Def_DetDLP_OpenAIAppendixD
import Definitions.Def_DetDLP_TerminalBTN
import Definitions.Def_DetDLP_FactorBase
set_option autoImplicit false
open DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

open DetDLP.D4Plan

theorem solution (hOAI : OpenAIAppendixDPremise) :
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
  obtain ⟨A,oa,e,L,P,bits,en,src⟩ := d4_partial_unroll_rank_enumerator_v2 hOAI.one_step_packet_hermite_mode C c hC hc E o
  obtain ⟨B,ob,k,bnd⟩ := src hOAI.closed_schedule_contraction
  obtain ⟨D,od,d,dig⟩ := d4_residual_digit_entry_machine C c k e B A ob oa
  obtain ⟨F,of₀,s,small⟩ := d4_small_regime_terminal_machine C c hC hc E o L
  obtain ⟨M,om,K,hM⟩ := d4_outer_scalar_cursor_machine_v2 (lemma_5_2_from_appendix_d hOAI) C c hC hc E o L e s d A F D oa of₀ od small
    (fun x hl he => ⟨P x hl he,bits x hl he,en x hl he,dig _ (en x hl he) (bnd x hl he)⟩)
  refine ⟨M,om,K,?_⟩
  intro b m k S p l desc G A hb hm hk bm mb hS hu hl hp ps ha am nv spec bounded ev Z
  let x : Input C c := ⟨b,m,k,S,p,l,desc,G,spec,A,hb,hm,hk,bm,mb,hS,hu,hl,hp,ps,ha,am,nv,bounded⟩
  refine ⟨0,1,fun _ i => Z.coeff i.val,by simp,?_⟩
  have conv (q : ℕ) (z : ℤ) : (z : ZMod (2^(0+q))).val = (z : ZMod (2^q)).val := by
    rw [Nat.zero_add]
  simp only [Finset.univ_unique,Finset.sum_singleton,pow_zero,Nat.div_one]
  have eq : (List.ofFn fun i : Fin l => (Z.coeff i.val : ZMod (2^(0+p))).val) = (List.ofFn fun i : Fin l => (Z.coeff i.val : ZMod (2^p)).val) := congrArg List.ofFn (funext fun i => conv p (Z.coeff i.val))
  rw [eq]
  exact hM x ev
