-- Prove2me | solution 1 for DetDLP.d4_stopped_continuation_bridge
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T09:16:37.719178+00:00
-- url     : https://prove2.me/submissions/a3cc32de-d1b0-485e-b097-38a02f07caf4

import Theorems.Thm_DetDLP_d4_stopped_local_entry_machine
import Theorems.Thm_DetDLP_D3Stopped_d3_stopped_core_continuation_machine
import Theorems.Thm_DetDLP_d4_residue_lift_eq
import Definitions.Def_DetDLP_PolyTBridge
set_option autoImplicit false
set_option maxHeartbeats 800000
open Polynomial DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle DetDLP.D4StoppedNode
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

namespace DetDLP.D4StoppedNode
private theorem flen (z : Bits) : (Encoding.frame z).length = 2*z.length+1 := by
  induction z with
  | nil => rfl
  | cons b z ih => change (Encoding.frame z).length+1+1 = 2*(z.length+1)+1; omega

private theorem widen (a n m : ℕ) (hn : 2 ≤ m) (hm : n+1 ≤ m) :
    polyBound a n ≤ (m:ℝ)^(2*a+1) := by
  rw [polyBound]
  have h₀ : (a:ℝ) ≤ (m:ℝ)^a := by exact_mod_cast (Nat.lt_two_pow_self (n:=a)).le.trans (Nat.pow_le_pow_left hn _)
  have h₁ : ((n:ℝ)+1)^a ≤ (m:ℝ)^a := by gcongr; exact_mod_cast hm
  have h := mul_le_mul h₀ h₁ (by positivity) (by positivity)
  rw [←pow_add] at h
  exact h.trans (pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ m by omega)) (by omega))

/-- The stopped branch on the canonical *pinned BTN instance* called by the outer dispatcher.
    The explicit factor T is the integer budget passed to the continuation; no Plan is quantified. -/
theorem stoppedContinuation (hClosed : AppendixD4.Closed) (C c : ℕ) (hC : 0 < C)
    (E F : PrimitiveMachine) (oE : Fin E.tapeCount) (oF : Fin F.tapeCount) :
    ∃ (B : PrimitiveMachine) (ob : Fin B.tapeCount) (k L₀ r : ℕ),
    ∀ (S P q l d deg : ℕ) (origDesc : Bits) (origG G : Graph) (f : ℤ[X]) (hf : f.Monic)
      (s : StoppedSpec origG G f l P deg) (A : Tensor origG (Fin l → ℕ))
      (α : Fin deg → Bool) (To Tp : ℕ),
      let payload := s.payload origDesc α
      let n := S+payload.length
      let desc := D3Stopped.descOf d f payload
      let m := S+desc.length
      let T := (r+1)*(n+1)^r*(To+Tp)
      D3Stopped.level S ≥ L₀ → G.nE ≤ C*S/8^d → G.maxDeg ≤ D3Stopped.cap S →
      G.nV ≤ (m+1)^c → 1 ≤ P → P ≤ S+80*C*S*(if d=0 then 1 else 2^D3Stopped.shift S (d-1)) →
      1 ≤ l → l ≤ C*S → RingOK f → f.natDegree = 4*D3Stopped.level S → P ≤ q →
      1 ≤ To → 1 ≤ Tp → (∀ v t j, A v t j < 2^P) →
      (∀ (w : Fin G.nV) (β : Fin (G.deg w) → Bool), (encodePortQuery desc w.val (List.ofFn β)).length ≤ c*(n+1)^c) →
      (∀ v t, let inp := encodePortQuery origDesc v.val (List.ofFn t)
              let ans := encodeNatListBin (List.ofFn (A v t))
              inp.length ≤ c*(n+1)^c ∧ ans.length ≤ c*(n+1)^c ∧ RunsWithin E oE inp ans To (polyBound c n)) →
      (∀ w pkt (h : s.vTable w = .pkt pkt) β, let p := s.packet w pkt h
              let inp := Encoding.encodeList id [pkt,List.ofFn β]
              let ans := residue f l p.creation hf (p.entry β)
              inp.length ≤ c*(n+1)^c ∧ ans.length ≤ c*(n+1)^c ∧ RunsWithin F oF inp ans Tp (polyBound c n)) →
      RunsWithin B ob (encodeBTNInstance desc G S P l) (residue f l q hf (s.value hf A q α))
        (polyBound k m * T * (2:ℝ)^((k:ℝ)*S/Real.sqrt (D3Stopped.level S : ℝ))) (polyBound k m) := by
  obtain ⟨L,o,r,hr⟩ := d4_stopped_local_entry_machine E F oE oF c
  let e := max c (2*r+1)
  have he : 0 < e := by dsimp [e]; omega
  obtain ⟨B,ob,k,L₀,H⟩ := D3Stopped.d3_stopped_core_continuation_machine hClosed C e hC he L o
  refine ⟨B,ob,k,L₀,r,?_⟩
  intro S P q l d deg origDesc origG G f hf s A α To Tp payload n desc m T hlevel hGE hGD hV hP hPu hl hlu hfOK hfdeg hq hTo hTp hAm hIn hO hPkt
  have hn : n+1 ≤ m ∧ 2 ≤ m := by
    simp only [n,m,desc,D3Stopped.descOf,Encoding.encodeList,id_eq,List.length_cons,List.length_append,List.length_nil,flen]; omega
  have localRun := hr S P l d deg origDesc origG G f hf s A α To Tp hTo hTp hAm hIn hO hPkt
  have hT : 1 ≤ T := by change 0 < (r+1)*(n+1)^r*(To+Tp); positivity
  have hspace := (widen r n m hn.2 hn.1).trans (pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ m by omega)) (le_max_right c (2*r+1)))
  have htime : polyBound r n * ((To:ℝ) + Tp) ≤ T := by
    dsimp [T,polyBound]; push_cast; gcongr; linarith
  have hv' := hV.trans (Nat.pow_le_pow_right (by omega) (le_max_left c (2*r+1)))
  rw [StoppedSpec.value, (d4_residue_lift_eq f l P q hf hq).1]
  exact H S P l T d payload G f hf (s.entry hf A α) hlevel hT hGE hGD hv' hP hPu hl hlu hfOK hfdeg
    (fun w β => PolyTBridge.runsWithin_mono_local (localRun w β) htime hspace)
end DetDLP.D4StoppedNode

open Polynomial DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle DetDLP.D4StoppedNode OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
theorem solution (hClosed : AppendixD4.Closed) (C c : ℕ) (hC : 0 < C)
    (E F : PrimitiveMachine) (oE : Fin E.tapeCount) (oF : Fin F.tapeCount) :
    ∃ (B : PrimitiveMachine) (ob : Fin B.tapeCount) (k L₀ r : ℕ),
    ∀ (S P q l d deg : ℕ) (origDesc : Bits) (origG G : Graph) (f : ℤ[X]) (hf : f.Monic)
      (s : StoppedSpec origG G f l P deg) (A : Tensor origG (Fin l → ℕ))
      (α : Fin deg → Bool) (To Tp : ℕ),
      let payload := s.payload origDesc α
      let n := S+payload.length
      let desc := D3Stopped.descOf d f payload
      let m := S+desc.length
      let T := (r+1)*(n+1)^r*(To+Tp)
      D3Stopped.level S ≥ L₀ → G.nE ≤ C*S/8^d → G.maxDeg ≤ D3Stopped.cap S →
      G.nV ≤ (m+1)^c → 1 ≤ P → P ≤ S+80*C*S*(if d=0 then 1 else 2^D3Stopped.shift S (d-1)) →
      1 ≤ l → l ≤ C*S → RingOK f → f.natDegree = 4*D3Stopped.level S → P ≤ q →
      1 ≤ To → 1 ≤ Tp → (∀ v t j, A v t j < 2^P) →
      (∀ (w : Fin G.nV) (β : Fin (G.deg w) → Bool), (encodePortQuery desc w.val (List.ofFn β)).length ≤ c*(n+1)^c) →
      (∀ v t, let inp := encodePortQuery origDesc v.val (List.ofFn t)
              let ans := encodeNatListBin (List.ofFn (A v t))
              inp.length ≤ c*(n+1)^c ∧ ans.length ≤ c*(n+1)^c ∧ RunsWithin E oE inp ans To (polyBound c n)) →
      (∀ w pkt (h : s.vTable w = .pkt pkt) β, let p := s.packet w pkt h
              let inp := Encoding.encodeList id [pkt,List.ofFn β]
              let ans := residue f l p.creation hf (p.entry β)
              inp.length ≤ c*(n+1)^c ∧ ans.length ≤ c*(n+1)^c ∧ RunsWithin F oF inp ans Tp (polyBound c n)) →
      RunsWithin B ob (encodeBTNInstance desc G S P l) (residue f l q hf (s.value hf A q α))
        (polyBound k m * T * (2:ℝ)^((k:ℝ)*S/Real.sqrt (D3Stopped.level S : ℝ))) (polyBound k m) := by
  exact DetDLP.D4StoppedNode.stoppedContinuation hClosed C c hC E F oE oF
