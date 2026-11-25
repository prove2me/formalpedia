-- Prove2me | solution 1 for DetDLP.lemma_5_2_from_appendix_d
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T06:55:51.975849+00:00
-- url     : https://prove2.me/submissions/ea443a97-771b-41ab-a6b6-69ba02018931

import Mathlib
import Definitions.Def_DetDLP_OpenAIAppendixD
import Definitions.Def_DetDLP_BTN
import Theorems.Thm_DetDLP_d1_schedule_poly
import Theorems.Thm_DetDLP_d1_schedule_active_and_exponent

set_option autoImplicit false
namespace DetDLP
open AppendixD4 OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open Polynomial

noncomputable abbrev D1Rho (b : ℕ) (G : BipartiteMultigraph) := max 1 ⌊Real.logb 2 ((b:ℝ) / (max G.maxDeg ⌈(b:ℝ)^((9:ℝ)/10)⌉₊ : ℕ))⌋₊

def D1ScheduleTheorem : Prop := ∀ C c0 : ℕ, 0 < C → 0 < c0 →
  ∃ (B c L : ℕ) (S : PrimitiveMachine) (o : Fin S.tapeCount), 0 < B ∧ 0 < c ∧ c0 ≤ c ∧
    ∀ (b P l : ℕ) (desc : List Bool) (G : BipartiteMultigraph),
    2 ≤ b → G.nE ≤ C*b → G.nV ≤ b ^ c0 → 1 ≤ P → P ≤ C*b → 1 ≤ l → l ≤ C*b →
    ∃ s : Schedule, s.start = 0 ∧ P ≤ (b+1)^c ∧
      RunsWithin S o (encodeBTNInstance desc G b P l) (s.bits X)
        (polyBound c (b+desc.length)) (polyBound c (b+desc.length)) ∧
      (s.H < G.nE → G.maxDeg ≤ s.cap ∧ s.cap ≤ C*b ∧ 0 < s.κ ∧ 2^s.κ ≤ (b+2)^c ∧ Active s (C*b) P B) ∧
      exponent s b ≤ (L:ℝ)*b / Real.sqrt (D1Rho b G : ℝ)

private theorem monoRun {M : PrimitiveMachine} {o : Fin M.tapeCount} {i w : List Bool} {t s t' s' : ℝ}
    (h : RunsWithin M o i w t s) (ht : t ≤ t') (hs : s ≤ s') : RunsWithin M o i w t' s' := by
  obtain ⟨a,b,c,d,e,f,g⟩ := h
  exact ⟨a,b,c,d,e,f.trans ht,fun k v hk hv => (g k v hk hv).trans hs⟩

theorem d1m13_of_schedule (hOAI : OpenAIAppendixDPremise) (sched : D1ScheduleTheorem) :
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
                (polyBound K (β + desc.length)) := by
  intro C c0 hC hc0 E oE
  obtain ⟨B,c,L,S,oS,hB,hc,hcc,hS⟩ := sched C c0 hC hc0
  obtain ⟨M,o,k,hM⟩ := hOAI.closed_schedule_contraction C c B hC hc hB S E oS oE
  let K := k*(L+1)
  have hkK : k ≤ K := by dsimp [K]; nlinarith
  refine ⟨M,o,K,?_⟩
  intro b P l Told desc G T hb ht he hv hP hP' hl hl' hE
  obtain ⟨s,hStart,hPrec,hGen,hAct,hExp⟩ := hS b P l desc G hb he hv hP hP' hl hl'
  let e := truncPolyEquiv P l
  let U : Tensor G (ResidualScalarOracle.B X l P) := fun v a => e (T v a)
  have hmap : BTNContract G U = e (BTNContract G T) := by simp [U,BTNContract]
  have hres := hM b P l Told desc G X monic_X U s hb ht (by simpa [hStart] using he) (by
    apply hv.trans
    exact (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) hcc)) hP hPrec hl hl' ringOK_X (by simpa using hP.trans hPrec) hGen (by
    intro v a
    obtain ⟨z,hz,hr⟩ := hE v a
    rw [(encodesTruncPoly_iff_residue P l z _).mp hz] at hr
    apply monoRun hr le_rfl
    apply pow_le_pow_right₀ _ hcc
    exact_mod_cast (show 1 ≤ b + desc.length by omega)) (by
    intro h
    obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := hAct h
    exact ⟨h₁,h₂,h₃,h₄,Or.inr (by simp),h₅⟩)
  rw [hmap] at hres
  refine ⟨_,(encodesTruncPoly_iff_residue ..).mpr rfl,monoRun hres ?_ ?_⟩
  · have hkpoly : polyBound k (b+desc.length) ≤ polyBound K (b+desc.length) := by
      unfold polyBound
      apply mul_le_mul (by exact_mod_cast hkK) (pow_le_pow_right₀ (by have := Nat.cast_nonneg (α:=ℝ) (b+desc.length); linarith) hkK) (by positivity) (by positivity)
    apply mul_le_mul (mul_le_mul_of_nonneg_right hkpoly (by positivity)) ?_ (by positivity) (by unfold polyBound; positivity)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    change (k:ℝ)*exponent s b ≤ (K:ℝ)*b / Real.sqrt (D1Rho b G : ℝ)
    calc (k:ℝ)*exponent s b ≤ (k:ℝ)*((L:ℝ)*b/Real.sqrt (D1Rho b G : ℝ)) := by gcongr
      _ = ((k*L:ℕ):ℝ)*b/Real.sqrt (D1Rho b G : ℝ) := by push_cast; ring
      _ ≤ _ := by gcongr; exact_mod_cast (show k*L ≤ K by dsimp [K]; nlinarith)
  · unfold polyBound
    apply mul_le_mul (by exact_mod_cast hkK) (pow_le_pow_right₀ (by have := Nat.cast_nonneg (α:=ℝ) (b+desc.length); linarith) hkK) (by positivity) (by positivity)

end DetDLP
namespace DetDLP.D1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private theorem flen (w : List Bool) : (Encoding.frame w).length = 2*w.length+1 := by
  induction w with
  | nil => rfl
  | cons b w ih => change (Encoding.frame w).length + 1 + 1 = 2*(w.length+1)+1; omega

private theorem cwlen (n : ℕ) : (countWord n).length ≤ n+1 := by
  by_cases h : n=0
  · simp [h,countWord]
  · simp only [countWord,if_neg h,Nat.size_eq_bits_len]; exact (Nat.size_le.mpr n.lt_two_pow_self).trans (Nat.le_succ _)

private theorem epslen (G : BipartiteMultigraph) (es : List (Fin G.nE)) :
    (encodeNatListBin (es.flatMap fun e => [(G.endpoints e).1.val,(G.endpoints e).2.val])).length ≤ (4*G.nV+8)*es.length+1 := by
  induction es with
  | nil => simp [encodeNatListBin,Encoding.encodeList]
  | cons e es ih =>
    simp only [List.flatMap_cons,List.cons_append,List.nil_append,encodeNatListBin,Encoding.encodeList,List.length_cons,List.length_append,flen] at *
    have h := cwlen (G.endpoints e).1.val
    have h' := cwlen (G.endpoints e).2.val
    have h1 := (G.endpoints e).1.isLt; have h2 := (G.endpoints e).2.isLt; nlinarith

theorem input_bound {b P l C c0 : ℕ} (G : BipartiteMultigraph) (w : List Bool) (hb : 2 ≤ b)
    (he : G.nE ≤ C*b) (hv : G.nV ≤ b^c0) (hp : P ≤ C*b) (hl : l ≤ C*b) :
    (encodeBTNInstance w G b P l).length + 1 ≤ (256*(C+1)^2)*(b+w.length+1)^(2*(c0+1)) := by
  let N := b+w.length+1
  let T := (C+1)*N^(c0+1)
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hNt : N ≤ N^(c0+1) := by simpa using (Nat.pow_le_pow_right hN (show 1 ≤ c0+1 by omega))
  have hT : N^(c0+1) ≤ T := by dsimp [T]; rw [mul_comm]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hV : G.nV ≤ T := hv.trans ((Nat.pow_le_pow_left (by dsimp [N]; omega : b ≤ N) _).trans ((Nat.pow_le_pow_right hN (Nat.le_succ _)).trans hT))
  have hCt : C*b ≤ T := Nat.mul_le_mul (by omega : C ≤ C+1) (le_trans (by dsimp [N]; omega : b ≤ N) hNt)
  have hE := he.trans hCt
  have hET := Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hV) 8) hE
  have hEp := epslen G (List.finRange G.nE); rw [List.length_finRange] at hEp
  have hG : G.encode.length ≤ 8*T^2+30*T+24 := by
    simp only [BipartiteMultigraph.encode,Encoding.encodeList,id_eq,List.length_append,List.length_cons,flen,List.length_ofFn,List.length_nil]
    nlinarith only [hEp,hET,cwlen G.nV,cwlen G.nE,hV,hE]
  have h1 : w.length ≤ T := le_trans (by dsimp [N]; omega : w.length ≤ N) (hNt.trans hT)
  have h2 : b ≤ T := (by dsimp [N]; omega : b ≤ N).trans (hNt.trans hT)
  have hT2 : 1 ≤ T := hN.trans (hNt.trans hT)
  have hT3 : T ≤ T^2 := by simpa [pow_two] using Nat.le_mul_of_pos_right T hT2
  have hRw : (256*(C+1)^2)*N^(2*(c0+1)) = 256*T^2 := by dsimp [T]; rw [mul_comm 2 (c0+1),pow_mul]; ring
  change _ ≤ (256*(C+1)^2)*N^(2*(c0+1)); rw [hRw]
  simp only [encodeBTNInstance,Encoding.encodeList,id_eq,List.length_append,List.length_cons,flen,List.length_nil]
  nlinarith only [hG,cwlen b,cwlen P,cwlen l,h1,h2,hp.trans hCt,hl.trans hCt,hT2,hT3]

theorem enlarge {i n a f k c : ℕ} (hi : i+1 ≤ a*(n+1)^f) (hc : k*a^k ≤ c) (he : f*k ≤ c) :
    polyBound k i ≤ polyBound c n := by
  have h : k*(i+1)^k ≤ c*(n+1)^c := calc
    _ ≤ k*(a*(n+1)^f)^k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hi _)
    _ = (k*a^k)*(n+1)^(f*k) := by rw [mul_pow,pow_mul]; ring
    _ ≤ _ := Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) he)
  unfold polyBound; exact_mod_cast h
end DetDLP.D1
namespace DetDLP
open D1 AppendixD4
theorem d1_schedule_verified : D1ScheduleTheorem := by
  intro C c0 hC hc0
  obtain ⟨hpoly,henc⟩ := d1_schedule_poly C hC
  obtain ⟨S,o,k,hS⟩ := PolyTBridge.polyT_listBool_runsWithin _ hpoly
  let a := 256*(C+1)^2
  let f := 2*(c0+1)
  let c := c0+4*(8*C+1)+k*a^k+f*k+C+2
  have hk : k*a^k ≤ c := by dsimp [c]; omega
  have hf : f*k ≤ c := by dsimp [c]; omega
  have hc : 4*(8*C+1) ≤ c := by dsimp [c]; omega
  refine ⟨81*C+544,c,C*threshold C+1024,S,o,by omega,by dsimp [c]; omega,by dsimp [c]; omega,?_⟩
  intro b P l desc G hb he hv hP hP' hl hl'
  obtain ⟨hst,hact,hex⟩ := d1_schedule_active_and_exponent (deg:=G.maxDeg) hC hb he hP'
  have hrun := hS (encodeBTNInstance desc G b P l)
  rw [henc] at hrun
  have hsize := enlarge (k:=k) (a:=a) (f:=f) (input_bound G desc hb he hv hP' hl') hk hf
  have hCb : C*b ≤ (b+1)^c := calc
    _ ≤ (b+1)^C*(b+1) := Nat.mul_le_mul ((Nat.lt_two_pow_self (n:=C)).le.trans (Nat.pow_le_pow_left (by omega) _)) (Nat.le_succ b)
    _ = (b+1)^(C+1) := (pow_succ ..).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by dsimp [c]; omega)
  refine ⟨_,hst,hP'.trans hCb,monoRun hrun hsize hsize,?_,hex⟩
  intro h; obtain ⟨ha,hb',hk',hk'',hA⟩ := hact h
  exact ⟨ha,hb',hk',hk''.trans (Nat.pow_le_pow_right (by omega) hc),hA⟩
end DetDLP
open DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
theorem solution (hOAI : OpenAIAppendixDPremise) :
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
                (polyBound K (β + desc.length)) := d1m13_of_schedule hOAI d1_schedule_verified
