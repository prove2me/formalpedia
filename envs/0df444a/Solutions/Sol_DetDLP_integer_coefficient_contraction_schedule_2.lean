-- Prove2me | solution 2 for DetDLP.integer_coefficient_contraction_schedule
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T15:57:39.454659+00:00
-- url     : https://prove2.me/submissions/f6afab29-24cc-486d-82ad-4c7ff9eb6d90
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_DetDLP_scalar_contraction_stack_driver
import Theorems.Thm_DetDLP_bounded_entry_evaluator_stack_simulation
import Definitions.Def_DetDLP_Machine
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_CompileSpace_compile_word_answer_space

namespace DetDLP.ContractionStackBounds
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
abbrev cap (k u : ℕ) := k*(u+1)^k
def raised (s k : ℕ) := 20*(s+1)*(k+1)
theorem le_raised (s k : ℕ) : k≤raised s k := by unfold raised; nlinarith [Nat.zero_le s,Nat.zero_le (s*k)]
theorem cost (s k u : ℕ) :
    7*cap k u≤cap (raised s k) u ∧ s*(2*cap k u+15)≤cap (raised s k) u := by
  let K := raised s k
  have le : (u+1)^k≤(u+1)^K := Nat.pow_le_pow_right (by omega) (le_raised s k)
  have h1 : 1≤(u+1)^K := Nat.one_le_pow _ _ (by omega)
  have h7 : 7*k≤K := by dsimp [K,raised]; nlinarith only [Nat.zero_le s,Nat.zero_le (s*k),Nat.zero_le k]
  have hs : s*(2*k+15)≤K := by dsimp [K,raised]; nlinarith only [Nat.zero_le s,Nat.zero_le (s*k),Nat.zero_le k]
  constructor
  · unfold cap; rw [← Nat.mul_assoc]; exact Nat.mul_le_mul h7 le
  · calc
      _ ≤ s*((2*k+15)*(u+1)^K) := by
        apply Nat.mul_le_mul_left
        have hk := Nat.mul_le_mul_left (2*k) le
        dsimp [cap]; nlinarith only [hk,h1]
      _=(s*(2*k+15))*(u+1)^K := by ring
      _≤_ := Nat.mul_le_mul_right _ hs

theorem time_bound (s k u len n : ℕ) (T X : ℝ) (ht : 0≤T) (hx : 0≤X) (hlen : len≤7*n)
    (steps : (n:ℝ)≤polyBound k u*T*(2:ℝ)^((k:ℝ)*X)) :
    (len:ℝ)≤polyBound (raised s k) u*T*(2:ℝ)^((raised s k:ℝ)*X) := by
  have h7 := (cost s k u).1
  have a : (7:ℝ)*polyBound k u≤polyBound (raised s k) u := by unfold polyBound; exact_mod_cast h7
  have nonneg : 0≤polyBound (raised s k) u := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by exact_mod_cast Nat.zero_le (u+1)) _)
  have b : (2:ℝ)^((k:ℝ)*X)≤2^((raised s k:ℝ)*X) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast le_raised s k) hx
  calc
      (len:ℝ)≤7*(n:ℝ) := by exact_mod_cast hlen
      _≤7*(polyBound k u*T*2^((k:ℝ)*X)) := mul_le_mul_of_nonneg_left steps (by norm_num)
      _=(7*polyBound k u)*T*2^((k:ℝ)*X) := by ring
      _≤_ := mul_le_mul (mul_le_mul_of_nonneg_right a ht) b (Real.rpow_nonneg (by norm_num) _) (mul_nonneg nonneg ht)

set_option maxHeartbeats 800000 in
theorem compile {r s l : ℕ} (p : BitProgram.Program r s l) (out : Fin s) (k u : ℕ) (T X : ℝ) (ht : 0≤T) (hx : 0≤X)
    (input word : List Bool) {n : ℕ} {z : BitProgram.Cfg r s l}
    (tr : BitProgram.Trace p n (BitProgram.initial p input) z)
    (halt : z.pc=none) (val : z.stacks out=word) (flag : z.stacks p.outputStack=[true])
    (steps : (n:ℝ)≤polyBound k u*T*(2:ℝ)^((k:ℝ)*X))
    (space : ∀ j c,j≤n→ BitProgram.Trace p j (BitProgram.initial p input) c→∀ i,(c.stacks i).length≤cap k u) :
    RunsWithin (GuardedCompiler.primitive p) out input word
      (polyBound (raised s k) u*T*(2:ℝ)^((raised s k:ℝ)*X)) (polyBound (raised s k) u) := by
  obtain ⟨len,hlen,cf,trace,hstate,hw,_,hspace⟩ := CompileSpace.compile_word_answer_space p out tr halt val flag space
  have inputB := space 0 (BitProgram.initial p input) (by omega) (.refl _) p.inputStack
  simp only [BitProgram.initial,ite_true,if_true] at inputB
  have hI : input.length≤cap k u := by simpa [BitProgram.initial] using inputB
  obtain ⟨h7,hS⟩ := cost s k u
  refine ⟨len,cf,trace,⟨true,hstate⟩,hw,time_bound s k u len n T X ht hx hlen steps,?_⟩
  intro j c hj hc
  have hs := hspace j c hj hc
  have H : visitedSpace c≤cap (raised s k) u := hs.trans ((Nat.mul_le_mul_left _ (by omega)).trans hS)
  unfold polyBound; exact_mod_cast H
end DetDLP.ContractionStackBounds

open DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution :
    ∀ (C c0 : ℕ), 0 < C → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin ℓ' → ℕ),
            2 ≤ β →
            1 ≤ Told →
            G.nE ≤ C * β →
            G.nV ≤ β ^ c0 →
            1 ≤ P → P ≤ C * β →
            1 ≤ ℓ' → ℓ' ≤ C * β →
            (∀ v t i, A v t i < 2^P) →
            (∀ v t, RunsWithin E outE (encodePortQuery desc v.val (List.ofFn t))
              (encodeNatListBin (List.ofFn (A v t))) (Told : ℝ) (((β+desc.length : ℕ) : ℝ)^c0)) →
            let Δbar : ℕ := max G.maxDeg (Nat.ceil ((β : ℝ) ^ ((9 : ℝ) / 10)))
            let ρ : ℕ := max 1 (Nat.floor (Real.logb 2 ((β : ℝ) / (Δbar : ℝ))))
            let Z := BTNContract G (fun v t => ∑ i : Fin ℓ',
              Polynomial.monomial i.val (A v t i : ℤ))
            let w := encodeNatListBin (List.ofFn fun i : Fin ℓ' =>
              ((Z.coeff i.val : ZMod (2^P)).val))
            RunsWithin M outM (encodeBTNInstance desc G β P ℓ') w
              (polyBound K (β+desc.length) * (Told : ℝ) * (2 : ℝ)^((K : ℝ) *
                ((β : ℝ)/Real.sqrt (ρ : ℝ) + ∑ d ∈ Finset.range (ρ+1),
                 ((β : ℝ)/(8 : ℝ)^d) / Real.sqrt ((ρ : ℝ)/(2 : ℝ)^d))))
              (polyBound K (β+desc.length)) := by
  intro C c0 hC hc0 E outE
  obtain ⟨se,le,Q,it,iv,ot,ov,hi,ho,ev⟩ := bounded_entry_evaluator_stack_simulation E outE
  obtain ⟨r,s,l,D,out,k,driver⟩ := scalar_contraction_stack_driver C c0 hC hc0 Q it iv ot ov hi ho
  refine ⟨GuardedCompiler.primitive D,out,ContractionStackBounds.raised s k,?_⟩
  intro β P ell Told desc G A hβ ht he hv hp hP hl hL ha heval Δ ρ Z w
  obtain ⟨n,z,tr,halt,value,flag,time,space⟩ :=
    driver β P ell Told desc G A hβ ht he hv hp hP hl hL ha (by
      intro v t regs q start
      have step := ev q (encodeNatListBin (List.ofFn (A v t))) (Told:ℝ)
        (((β+desc.length:ℕ):ℝ)^c0) (heval v t) regs
      obtain ⟨n,c,hn,htr,hhalt,hw,hsp⟩ := step
      refine ⟨n,c,by exact_mod_cast hn,htr,hhalt,hw,?_⟩
      intro j b hj htr i
      have bound := hsp j b hj htr i
      have cast : (((β+desc.length:ℕ):ℝ)^c0)=(((β+desc.length)^c0:ℕ):ℝ) := by push_cast; rfl
      rw [cast,Nat.floor_natCast] at bound; exact bound)
  let X := (β:ℝ)/Real.sqrt (ρ:ℝ)+∑ d∈Finset.range (ρ+1),((β:ℝ)/(8:ℝ)^d)/Real.sqrt ((ρ:ℝ)/(2:ℝ)^d)
  have hx : 0≤X := by dsimp [X]; positivity
  exact ContractionStackBounds.compile D out k (β+desc.length) Told X (Nat.cast_nonneg _) hx
    (encodeBTNInstance desc G β P ell) w tr halt value flag time space
