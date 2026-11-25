-- Prove2me | solution 1 for DetDLP.D3Stopped.d3_stopped_core_continuation_machine
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T07:16:46.965548+00:00
-- url     : https://prove2.me/submissions/30c78f2a-1504-4af4-bdf9-106e1873654e

import Theorems.Thm_DetDLP_D3Stopped_d3_stopped_schedule_poly
import Theorems.Thm_DetDLP_D3Stopped_d3_stopped_schedule_raw_poly
import Theorems.Thm_DetDLP_D3Stopped_d3_stopped_schedule_active
import Definitions.Def_DetDLP_PolyTBridge

set_option autoImplicit false
namespace DetDLP.D3Stopped
open Polynomial AppendixD4 OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open OAI.Algorithms.SubexponentialSAT.Computation
private theorem flen (w : Bits) : (Encoding.frame w).length = 2*w.length+1 := by
  induction w with
  | nil => rfl
  | cons b w ih => change (Encoding.frame w).length+1+1=2*(w.length+1)+1; omega
private theorem clen (n : ℕ) : (countWord n).length ≤ n+1 := by
  by_cases hn : n=0
  · subst n; decide
  · simp only [countWord,if_neg hn,Nat.size_eq_bits_len]; exact (Nat.size_le.2 Nat.lt_two_pow_self).trans (Nat.le_succ n)
private theorem elen (xs : List ℕ) (N : ℕ) (h : ∀ n ∈ xs, n ≤ N) :
    (encodeNatListBin xs).length ≤ (2*N+4)*xs.length+1 := by
  induction xs with
  | nil => simp [encodeNatListBin,Encoding.encodeList]
  | cons n xs ih =>
    have h1 := h n (by simp); have h2 := ih (fun k hk => h k (by simp [hk]))
    change (true :: (Encoding.frame (countWord n) ++ encodeNatListBin xs)).length ≤ _
    simp only [List.length_cons,List.length_append,flen,Nat.mul_succ]; have := clen n; omega
private theorem inlen (G : Graph) (desc : Bits) (S P l N : ℕ) (hN : 32 ≤ N)
    (hV : G.nV ≤ N) (hE : G.nE ≤ N) (hd : desc.length ≤ N) (hS : S ≤ N) (hP : P ≤ N) (hl : l ≤ N) :
    (encodeBTNInstance desc G S P l).length + 1 ≤ N^4 := by
  let es := (List.finRange G.nE).flatMap fun e => [(G.endpoints e).1.val,(G.endpoints e).2.val]
  have he : es.length = 2*G.nE := by simp [es,List.length_flatMap,Nat.mul_comm]
  have hb : (encodeNatListBin es).length ≤ (2*N+4)*(2*N)+1 := by
    refine (elen _ N ?_).trans ?_
    · intro k hk; obtain ⟨e,_,hk⟩ := List.mem_flatMap.mp hk; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; rcases hk with rfl | rfl <;> exact (Fin.isLt _).le.trans hV
    · rw [he]; gcongr
  have hgraph : G.encode.length ≤ 8*N^2+25*N+20 := by
    change (Encoding.encodeList id [countWord G.nV,countWord G.nE,List.ofFn G.side,encodeNatListBin es]).length ≤ _
    simp only [Encoding.encodeList,id_eq,List.length_cons,List.length_append,flen,List.length_ofFn,List.length_nil]
    nlinarith [clen G.nV,clen G.nE]
  simp only [encodeBTNInstance,Encoding.encodeList,id_eq,List.length_cons,List.length_append,flen,List.length_nil]
  have hsq : 32*N ≤ N^2 := by nlinarith [Nat.mul_le_mul_right N hN]
  have hq : N^2*32^2 ≤ N^4 := by nlinarith [Nat.mul_le_mul_left (N^2) (Nat.pow_le_pow_left hN 2)]
  nlinarith [clen S,clen P,clen l]
private theorem shift_le (S t : ℕ) : shift S t ≤ level S := by
  have h : shift S t + 2 * width S t ≤ 4*(level S/131072) := by
    induction t with
    | zero => simp [shift,width]; omega
    | succ t ih =>
      have ht : shift S (t+1) = shift S t+2*width S (t+1) := by simp [shift,Finset.sum_range_succ,Nat.mul_add]
      have hw : width S (t+1) = width S t/2 := by simp only [width,Nat.div_div_eq_div_mul,pow_succ,Nat.mul_assoc]
      rw [ht,hw]; omega
  omega
private theorem pbmon {a b : ℕ} (hab : a ≤ b) (n : ℕ) : polyBound a n ≤ polyBound b n := by
  unfold polyBound; exact mul_le_mul (by exact_mod_cast hab) (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) hab) (by positivity) (by positivity)
private theorem _kNat {n : ℕ} (p : 1 ≤ n) {a b : ℕ} (h : a ≤ b) : n^a ≤ n^b := Nat.pow_le_pow_right p h

theorem _root_.solution
    (hClosed : AppendixD4.Closed) (C c : ℕ) (hC : 0 < C) (hc : 0 < c)
    (E : PrimitiveMachine) (oE : Fin E.tapeCount) :
    ∃ (A : PrimitiveMachine) (oA : Fin A.tapeCount) (K L₀ : ℕ),
      ∀ (S P l Told d₀ : ℕ) (payload : Bits) (G : Graph) (f : ℤ[X]) (hf : f.Monic)
        (T : Tensor G (ResidualScalarOracle.B f l P)),
        let desc := descOf d₀ f payload
        L₀ ≤ level S → 1 ≤ Told → G.nE ≤ C*S/8^d₀ → G.maxDeg ≤ cap S →
        G.nV ≤ (S+desc.length+1)^c → 1 ≤ P →
        P ≤ S+80*C*S*(if d₀=0 then 1 else 2^shift S (d₀-1)) →
        1 ≤ l → l ≤ C*S → RingOK f → f.natDegree = 4*level S →
        (∀ v α, RunsWithin E oE (encodePortQuery desc v.val (List.ofFn α))
          (residue f l P hf (T v α)) Told (((S+desc.length : ℕ) : ℝ)^c)) →
        RunsWithin A oA (encodeBTNInstance desc G S P l) (residue f l P hf (BTNContract G T))
          (polyBound K (S+desc.length)*(Told : ℝ)*(2:ℝ)^((K:ℝ)*(S:ℝ)/Real.sqrt (level S : ℝ)))
          (polyBound K (S+desc.length)) := by
  obtain ⟨B,L₀,hB,hA⟩ := d3_stopped_schedule_active C hC
  obtain ⟨hPoly,hSpec⟩ := d3_stopped_schedule_raw_poly C
  obtain ⟨Gen,oGen,j,hGen⟩ := PolyTBridge.polyT_listBool_runsWithin _ hPoly
  let b := c+5
  let q := b+4*b*j+j
  obtain ⟨A,oA,k,hRun⟩ := hClosed C q B hC (by dsimp [q,b]; omega) hB Gen E oGen oE
  let K := 1028*(k+1)
  refine ⟨A,oA,K,max L₀ (160*C+32),?_⟩
  intro S P l Told d₀ payload G f hf T desc hL hT hM hDeg hV hP hP' hl hl' hRing hF hE
  let n := S+desc.length; let s := schedule C S G.nE d₀
  let N := (n+1)^b
  have hLS : level S ≤ S := Nat.clog_le_of_le_pow ((Nat.lt_pow_self (n:=S) (by decide : 1<2)).le)
  have hlarge : 160*C+32 ≤ S := ((le_max_right ..).trans hL).trans hLS
  have hnp : 1 ≤ n := by dsimp [n]; omega
  have hbq : b ≤ q := by dsimp [q]; omega
  have hcq : c ≤ q := by dsimp [q,b]; omega
  have htw : 2^level S ≤ 2*S := by
    have h0 : 1 ≤ level S := by omega
    have hh : 2^(level S-1) < S := Nat.pow_lt_of_lt_clog (by omega : level S-1 < level S)
    calc _ = 2^(level S-1+1) := by congr 1; omega
         _ ≤ _ := by rw [pow_succ]; omega
  have hPV : P ≤ (S+1)^b := by
    have hu : (if d₀=0 then 1 else 2^shift S (d₀-1)) ≤ 2*S := by split; omega; exact (Nat.pow_le_pow_right (by decide) (shift_le ..)).trans htw
    apply hP'.trans
    calc _ ≤ S+80*C*S*(2*S) := by gcongr
         _ ≤ (S+1)^4 := by nlinarith [Nat.mul_le_mul_right (S^2) hlarge]
         _ ≤ _ := _kNat (by omega) (by dsimp [b]; omega)
  have hlN : C*S ≤ N := calc
    _ ≤ (n+1)^2 := by rw [pow_two]; apply Nat.mul_le_mul <;> dsimp [n] <;> omega
    _ ≤ _ := _kNat (by omega) (by dsimp [b]; omega)
  have hnN : n+1 ≤ N := (pow_one (n+1)).symm.le.trans (_kNat (by omega) (by dsimp [b]; omega))
  have hPn : P ≤ N := hPV.trans (Nat.pow_le_pow_left (by dsimp [n]; omega) _)
  have henc := inlen G desc S P l N (by dsimp [n] at hnN; omega) (hV.trans (_kNat (by omega) (by dsimp [b]; omega))) (hM.trans ((Nat.div_le_self ..).trans hlN)) (by dsimp [n] at hnN; omega) (by dsimp [n] at hnN; omega) hPn (hl'.trans hlN)
  have hbudget : polyBound j (encodeBTNInstance desc G S P l).length ≤ polyBound q n := by
    have hh := Nat.pow_le_pow_left henc j
    change _ ≤ (((n+1)^b)^4)^j at hh
    have hh' : ((encodeBTNInstance desc G S P l).length+1)^j ≤ (n+1)^q := by
      apply hh.trans; simp only [←pow_mul]; apply _kNat (by omega); dsimp [q]; nlinarith
    unfold polyBound; exact_mod_cast Nat.mul_le_mul (show j≤q by dsimp [q]; omega) hh'
  have hG := hGen (encodeBTNInstance desc G S P l)
  rw [show scheduleRaw C (encodeBTNInstance desc G S P l) = s.bits f from hSpec ..] at hG
  have hFq : f.natDegree ≤ (S+1)^q := by
    rw [hF]; calc _ ≤ (S+1)^2 := by nlinarith
                  _ ≤ _ := _kNat (by omega) (by dsimp [q,b]; omega)
  have hgRun := hRun S P l Told desc G f hf T s (by omega) hT hM (hV.trans (_kNat (by omega) hcq)) hP (hPV.trans (_kNat (by omega) hbq)) hl hl' hRing hFq (PolyTBridge.runsWithin_mono_local hG hbudget hbudget)
    (fun v α => PolyTBridge.runsWithin_mono_local (hE v α) le_rfl (pow_le_pow_right₀ (by exact_mod_cast hnp : (1:ℝ) ≤ n) hcq))
  have hr := hgRun (by
    intro hs; change min G.nE (threshold S) < G.nE at hs
    have hgt : threshold S < G.nE := by omega
    obtain ⟨h1,h2,h3,h4⟩ := hA S G.nE P d₀ ((le_max_left ..).trans hL) hgt hM hP hP'
    exact ⟨hDeg,h1,h2,h3.trans (_kNat (by omega) (by dsimp [q,b]; omega)),Or.inl hF,h4⟩)
  have hK : k ≤ K := by dsimp [K]; omega
  apply PolyTBridge.runsWithin_mono_local hr _ (pbmon hK n)
  apply mul_le_mul (mul_le_mul_of_nonneg_right (pbmon hK n) (by positivity)) _ (by positivity) (by unfold polyBound; positivity)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  calc (k:ℝ)*exponent s S ≤ (k:ℝ)*(1028*S/Real.sqrt (level S : ℝ)) := mul_le_mul_of_nonneg_left (d3_stopped_schedule_poly C S G.nE d₀ (by omega)) (by positivity)
       _ = (k*1028:ℝ)*S/Real.sqrt (level S:ℝ) := by ring
       _ ≤ _ := by gcongr; exact_mod_cast (by dsimp [K]; omega : k*1028 ≤ K)
end DetDLP.D3Stopped
