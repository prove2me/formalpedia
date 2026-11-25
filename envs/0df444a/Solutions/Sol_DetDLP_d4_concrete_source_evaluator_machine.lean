-- Prove2me | solution 1 for DetDLP.d4_concrete_source_evaluator_machine
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T09:23:13.411904+00:00
-- url     : https://prove2.me/submissions/45b3065a-cc5c-4b41-8b93-17491be7e04a

import Theorems.Thm_DetDLP_d4_residue_lift_eq
import Theorems.Thm_DetDLP_d4_outer_dispatch
import Theorems.Thm_DetDLP_d4_stopped_continuation_bridge
import Definitions.Def_DetDLP_PolyTBridge
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Definitions.Def_DetDLP_D4StoppedNode
set_option autoImplicit false
open DetDLP
private theorem linPow (t : ℕ) (ht : 6 ≤ t) : 4*t+5 ≤ 2^t := by
  induction t, ht using Nat.le_induction with
  | base => decide
  | succ t ht ih => rw [pow_succ]; omega

private theorem packetRate (K c S a : ℕ) (hL : 24 ≤ D3Stopped.level S)
    (ha : a ≤ D3Stopped.level S / 32768) :
    Real.exp ((K:ℝ) * (2^a:ℕ) * Real.log (((S+2)^c:ℕ):ℝ)) ≤
      (2:ℝ)^(((K*c:ℕ):ℝ)*S/Real.sqrt (D3Stopped.level S:ℝ)) := by
  let L := D3Stopped.level S
  change 24 ≤ L at hL
  change a ≤ L / 32768 at ha
  have hprev : L-1 < Nat.clog 2 S := by change L-1 < L; omega
  have hdown := (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).1 hprev
  have hsmall : L+2 ≤ 2^(L/4) := (show L+2 ≤ 4*(L/4)+5 by omega).trans (linPow _ (by omega))
  have hpow : 2^a*(L+2)*L ≤ S := calc
    _ ≤ 2^a*2^(L/4)*2^(L/4) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hsmall) (by omega)
    _ = 2^(a+L/4+L/4) := by simp only [pow_add]
    _ ≤ 2^(L-1) := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ S := hdown.le
  have hup : S ≤ 2^L := Nat.le_pow_clog (by decide) S
  have hup' : S+2 ≤ 2^(L+2) := by have := Nat.two_pow_pos L; rw [pow_add]; norm_num; omega
  have hlog := Real.log_le_log (by positivity : (0:ℝ)<((S+2:ℕ):ℝ)) (show ((S+2:ℕ):ℝ) ≤ (2:ℝ)^(L+2) by exact_mod_cast hup')
  rw [Real.log_pow] at hlog
  have hLr : (1:ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hs : Real.sqrt (L:ℝ) ≤ L := Real.sqrt_le_self_iff.2 (Or.inr hLr)
  have hspos : 0 < Real.sqrt (L:ℝ) := Real.sqrt_pos.2 (by linarith)
  have hpow' : (2:ℝ)^a*(L+2)*Real.sqrt (L:ℝ) ≤ S :=
    (mul_le_mul_of_nonneg_left hs (by positivity)).trans (by exact_mod_cast hpow)
  rw [Real.rpow_def_of_pos (by norm_num),Real.exp_le_exp]
  simp only [Nat.cast_pow,Real.log_pow,Nat.cast_mul,Nat.cast_ofNat]
  change _ ≤ Real.log 2 * (_ / Real.sqrt (L:ℝ))
  rw [←mul_div_assoc,le_div_iff₀ hspos]
  push_cast at hlog
  calc
    _ ≤ (K:ℝ)*2^a*(c*((L+2)*Real.log 2))*Real.sqrt (L:ℝ) := by gcongr; simpa using hlog
    _ = (K*c*Real.log 2)*((2:ℝ)^a*(L+2)*Real.sqrt (L:ℝ)) := by ring
    _ ≤ (K*c*Real.log 2)*S := by gcongr
    _ = _ := by ring

open DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle DetDLP.D4StoppedNode Polynomial Groundwork
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
private def Pn (c n : ℕ) := c*(n+1)^c
private theorem pPB (c : ℕ) : PB (Pn c) := ⟨c,fun _ => le_rfl⟩
private theorem pj (c d n m : ℕ) (h : c ≤ d) (g : n ≤ m) : Pn c n ≤ Pn d m := by unfold Pn; gcongr; omega
private theorem pcast (c n : ℕ) : (Pn c n : ℝ) = polyBound c n := by simp [Pn,polyBound]
private theorem pReal {c d n m : ℕ} (h : c ≤ d) (g : n ≤ m) : polyBound c n ≤ polyBound d m := by
  simp only [←pcast]; exact_mod_cast pj _ _ _ _ h g
private noncomputable def rate (k S : ℕ) : ℝ := (2:ℝ)^((k:ℝ)*S/Real.sqrt (D3Stopped.level S:ℝ))
private theorem rone (k S : ℕ) : 1 ≤ rate k S := Real.one_le_rpow (by norm_num) (by positivity)
private theorem rmono {k j : ℕ} (h : k ≤ j) (S : ℕ) : rate k S ≤ rate j S := by unfold rate; gcongr <;> norm_num
private theorem rprod (k j S : ℕ) : rate k S * rate j S = rate (k+j) S := by unfold rate; rw [←Real.rpow_add (by norm_num)]; push_cast; congr 1; ring
private theorem fl (z : Bits) : (Encoding.frame z).length = 2*z.length+1 := by induction z <;> simp_all [Encoding.frame] <;> omega

theorem solution (hClosed : AppendixD4.Closed)
    (C c K_pkt c_pkt : ℕ) (hC : 0 < C) (E F : PrimitiveMachine)
    (oE : Fin E.tapeCount) (oF : Fin F.tapeCount) :
    ∃ (B : PrimitiveMachine) (ob : Fin B.tapeCount) (K L₀ : ℕ),
    (∀ (S κ l q : ℕ) (origDesc : Bits) (R origG : Graph) (v : Fin R.nV) (j : Fin origG.nV)
      (α : Fin (origG.deg j) → Bool) (V : Tensor origG (Fin l → ℕ)) (f : ℤ[X]) (hf : f.Monic),
      let N := S+origDesc.length
      let u := encodePortQuery (lookupDesc origDesc j.val κ l q) v.val (List.ofFn α)
      let x := encodePortQuery origDesc j.val (List.ofFn α)
      let a := V j α
      let y := encodeNatListBin (List.ofFn a)
      κ = f.natDegree → κ ≤ u.length → (∀ t, a t < 2^q) →
      u.length ≤ c*(N+1)^c → x.length ≤ c*(N+1)^c → y.length ≤ c*(N+1)^c →
      RunsWithin E oE x y (polyBound c N) (polyBound c N) →
      RunsWithin B ob u (residue f l q hf (liftBase f l q a))
        (polyBound K N * (2:ℝ)^((K:ℝ)*S/Real.sqrt (D3Stopped.level S:ℝ))) (polyBound K N)) ∧
    (∀ (S P q l d₀ deg i : ℕ) (origDesc : Bits) (origG G_stop : Graph) (f : ℤ[X]) (hf : f.Monic)
      (s : StoppedSpec origG G_stop f l P deg) (V : Tensor origG (Fin l → ℕ)) (α : Fin deg → Bool),
      let N := S+origDesc.length
      let n := S+(s.payload origDesc α).length
      let desc := D3Stopped.descOf d₀ f (s.payload origDesc α)
      let m := S+desc.length
      let u := encodePortQuery (stoppedDesc origDesc S l P d₀ f G_stop s.tableBits) i (List.ofFn α)
      let x := encodeBTNInstance desc G_stop S P l
      let y := residue f l P hf (BTNContract G_stop (s.entry hf V α))
      L₀ ≤ D3Stopped.level S → D3Stopped.shift S (d₀-1) ≤ D3Stopped.level S / 32768 →
      G_stop.nE ≤ C*S/8^d₀ → G_stop.maxDeg ≤ D3Stopped.cap S → G_stop.nV ≤ (m+1)^c →
      1 ≤ P → P ≤ S+80*C*S*(if d₀=0 then 1 else 2^D3Stopped.shift S (d₀-1)) →
      1 ≤ l → l ≤ C*S → RingOK f → f.natDegree = 4*D3Stopped.level S → P ≤ q →
      (∀ v t j, V v t j < 2^P) → u.length ≤ c*(N+1)^c → x.length ≤ c*(N+1)^c → y.length ≤ c*(N+1)^c →
      (∀ (w : Fin G_stop.nV) (β : Fin (G_stop.deg w) → Bool),
        (encodePortQuery desc w.val (List.ofFn β)).length ≤ c*(n+1)^c) →
      (∀ v t, let inp := encodePortQuery origDesc v.val (List.ofFn t)
              let ans := encodeNatListBin (List.ofFn (V v t))
              inp.length ≤ c*(n+1)^c ∧ ans.length ≤ c*(n+1)^c ∧
              RunsWithin E oE inp ans (polyBound c n) (polyBound c n)) →
      (∀ w pkt (h : s.vTable w = .pkt pkt) β, let p := s.packet w pkt h
              let n_pkt := G_stop.nE+p.creation+4*D3Stopped.level S+l+2
              let inp := Encoding.encodeList id [pkt,List.ofFn β]
              let ans := residue f l p.creation hf (p.entry β)
              n_pkt ≤ (S+2)^c_pkt ∧ inp.length ≤ c*(n+1)^c ∧ ans.length ≤ c*(n+1)^c ∧
              RunsWithin F oF inp ans (Real.exp ((K_pkt:ℝ)*(2^D3Stopped.shift S (d₀-1):ℕ)*Real.log n_pkt))
                (polyBound K_pkt n_pkt)) →
      RunsWithin B ob u (residue f l q hf (s.value hf V q α))
        (polyBound K N * (2:ℝ)^((K:ℝ)*S/Real.sqrt (D3Stopped.level S:ℝ))) (polyBound K N)) := by
  let pkt := fun n => (n+2)^c_pkt
  have ppkt : PB pkt := by
    let z := fun n : ℕ => n+2
    have pz : PB z := PB.id'.add (PB.const 2)
    have qq (t : ℕ) : PB (fun n => (z n)^t) := by
      induction t with
      | zero => simpa using PB.const 1
      | succ t ih => simpa only [pow_succ] using ih.mul pz
    exact qq c_pkt
  obtain ⟨e₀,he₀⟩ := (pPB K_pkt).comp ppkt
  let e := max c e₀
  have ce : c ≤ e := le_max_left ..
  obtain ⟨A,oa,a,L,r,hA⟩ := d4_stopped_continuation_bridge hClosed C e hC E F oE oF
  let w := fun N => N + Pn c N
  have pw : PB w := PB.id'.add (pPB c)
  let D := fun N => (Pn a (w N)+1)*(Pn (r+1) (w N)+1)*(Pn e (w N)+4)
  have pD : PB D := ((((pPB a).comp pw).add (PB.const 1)).mul (((pPB (r+1)).comp pw).add (PB.const 1))).mul (((pPB e).comp pw).add (PB.const 4))
  obtain ⟨d',hd'⟩ := (pPB a).comp pw
  let d := max c d'
  have cd : c ≤ d := le_max_left ..
  obtain ⟨B,ob,b,hLook,hStop⟩ := d4_outer_dispatch E A oE oa d
  obtain ⟨k,hk⟩ := (pPB b).mul (pD.add ((pPB c).add (PB.const 1)))
  let J := K_pkt*c_pkt
  let K := max (max b k) (J+a)
  have hbk : b ≤ K := (le_max_left ..).trans (le_max_left ..)
  have hpK (N : ℕ) : polyBound b N * ((D N:ℝ) + ((Pn c N:ℝ)+1)) ≤ polyBound K N := by
    rw [←pcast,←pcast]; exact_mod_cast (hk N).trans (pj k K N N ((le_max_right ..).trans (le_max_left ..)) le_rfl)
  refine ⟨B,ob,K,max 24 L,?_,?_⟩
  · intro S κ l q origDesc R origG v j α V f hf N u x a₀ y hκ hwidth hv hu hx hy hE
    have liftLen {z : ℕ} (hz : z ≤ Pn c N) : z ≤ Pn d N := hz.trans (pj _ _ _ _ cd le_rfl)
    have tim : polyBound c N ≤ (Pn c N:ℝ)+1 := by rw [pcast]; linarith
    have h1 : (1:ℝ) ≤ (Pn c N:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) (Pn c N)]
    have run := hLook N v.val j.val κ l q origDesc (List.ofFn α) f hf a₀ ((Pn c N:ℝ)+1) hκ hwidth h1 hv (liftLen hu) (liftLen hx) (liftLen hy)
      (PolyTBridge.runsWithin_mono_local hE tim (pReal cd le_rfl))
    apply PolyTBridge.runsWithin_mono_local run _ (pReal hbk le_rfl)
    calc _ ≤ polyBound K N := (mul_le_mul_of_nonneg_left (show (Pn c N:ℝ)+1 ≤ (D N:ℝ)+((Pn c N:ℝ)+1) by linarith [Nat.cast_nonneg (α:=ℝ) (D N)]) (by unfold polyBound; positivity)).trans (hpK N)
         _ ≤ polyBound K N * rate K S := le_mul_of_one_le_right (by unfold polyBound; positivity) (rone ..)
  · intro S P q l d₀ deg i origDesc origG G f hf s V α N n desc m u x y hL hshift hG hdeg hv hP hPu hl hlu hfOK hfdeg hq hV hu hx hy hIn hE hF
    let U := w N
    have hdm : desc.length ≤ x.length := by simp [x,encodeBTNInstance,Encoding.encodeList,fl]; omega
    have hnm : n ≤ m := by simp [n,m,desc,D3Stopped.descOf,Encoding.encodeList,fl]; omega
    have hm : m ≤ U := by change S+desc.length ≤ (S+origDesc.length)+Pn c N; change x.length ≤ Pn c N at hx; omega
    have hn := hnm.trans hm
    let To := Pn e n+1
    let Tp := ⌈rate J S⌉₊
    have hTp : 1 ≤ Tp := Nat.ceil_pos.2 (lt_of_lt_of_le zero_lt_one (rone ..))
    have hpRate := packetRate K_pkt c_pkt S (D3Stopped.shift S (d₀-1)) (by omega) hshift
    have hcall := hA S P P l d₀ deg origDesc origG G f hf s V α To Tp (by omega) hG hdeg
      (hv.trans (Nat.pow_le_pow_right (by omega) ce)) hP hPu hl hlu hfOK hfdeg le_rfl (by dsimp [To]; omega) hTp hV
      (fun w β => (hIn w β).trans (pj _ _ _ _ ce le_rfl))
      (fun v t => ⟨(hE v t).1.trans (pj _ _ _ _ ce le_rfl),(hE v t).2.1.trans (pj _ _ _ _ ce le_rfl),
        PolyTBridge.runsWithin_mono_local (hE v t).2.2 (by dsimp [To]; push_cast; rw [pcast]; linarith [pReal ce (le_refl n)]) (pReal ce le_rfl)⟩) ?_
    case refine_1 =>
      intro w pkt h β
      obtain ⟨hs,hi,ho,run⟩ := hF w pkt h β
      refine ⟨hi.trans (pj _ _ _ _ ce le_rfl),ho.trans (pj _ _ _ _ ce le_rfl),PolyTBridge.runsWithin_mono_local run ?_ ?_⟩
      · apply le_trans _ (hpRate.trans (Nat.le_ceil (rate J S)))
        apply Real.exp_le_exp.2
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.log_le_log (by positivity); exact_mod_cast hs
      · simp only [←pcast]; apply Nat.cast_le.mpr
        exact (pj _ _ _ _ le_rfl hs).trans ((he₀ S).trans (pj _ _ _ _ (le_max_right ..) (show S ≤ n from Nat.le_add_right ..)))
    have hy0 : residue f l P hf (s.value hf V P α) = y := (d4_residue_lift_eq f l P P hf le_rfl).1 _
    rw [hy0] at hcall
    let Z := rate (J+a) S
    have hZ : 1 ≤ Z := rone ..
    have hD : 1 ≤ D N := by change 0 < (_+1)*(_+1)*(_+4); positivity
    have htau : (1:ℝ) ≤ (D N:ℝ)*Z := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hD) hZ
    have hTp' : (Tp:ℝ) ≤ rate J S + 1 := (Nat.ceil_lt_add_one (show 0 ≤ rate J S by linarith [rone J S])).le
    have hsum : ((To+Tp:ℕ):ℝ) ≤ ((Pn e U:ℝ)+4)*rate J S := by
      have ht : (Pn e n:ℝ) ≤ Pn e U := by exact_mod_cast pj e e n U le_rfl hn
      dsimp only [To]; push_cast
      nlinarith [rone J S,mul_nonneg (Nat.cast_nonneg (α:=ℝ) (Pn e U)) (sub_nonneg.mpr (rone J S))]
    have hfactor : (r+1)*(n+1)^r ≤ Pn (r+1) U + 1 := by
      apply Nat.le_trans _ (Nat.le_add_right _ 1); unfold Pn; gcongr <;> omega
    have hcSpace : polyBound a m ≤ polyBound d N := by
      rw [←pcast,←pcast]; exact_mod_cast (pj a a m U le_rfl hm).trans ((hd' N).trans (pj _ _ _ _ (le_max_right ..) le_rfl))
    have hcTime : polyBound a m * (((r+1)*(n+1)^r*(To+Tp):ℕ):ℝ) * rate a S ≤ (D N:ℝ)*Z := by
      have ha : polyBound a m ≤ (Pn a U:ℝ)+1 := by rw [←pcast]; exact_mod_cast ((pj a a m U le_rfl hm).trans (Nat.le_add_right _ 1))
      change _ ≤ (((Pn a U+1)*(Pn (r+1) U+1)*(Pn e U+4):ℕ):ℝ)*rate (J+a) S
      rw [←rprod]; push_cast
      calc _ ≤ ((Pn a U:ℝ)+1)*(((Pn (r+1) U:ℝ)+1)*(((Pn e U:ℝ)+4)*rate J S))*rate a S := by
                  push_cast at hsum; gcongr <;> first | exact_mod_cast hfactor | exact hsum | exact ha | exact zero_le_one.trans (rone ..)
           _ = _ := by ring
    have len {z : ℕ} (hz : z ≤ Pn c N) : z ≤ Pn d N := hz.trans (pj _ _ _ _ cd le_rfl)
    have run := hStop N i S P q l d₀ deg origDesc origG G f hf s V α ((D N:ℝ)*Z) hq htau (len hu) (len hx) (len hy)
      (PolyTBridge.runsWithin_mono_local hcall hcTime hcSpace)
    apply PolyTBridge.runsWithin_mono_local run _ (pReal hbk le_rfl)
    rw [←mul_assoc]; change _ ≤ polyBound K N * rate K S
    apply mul_le_mul _ (rmono (le_max_right ..) S) (by linarith [hZ]) (by unfold polyBound; positivity)
    apply le_trans _ (hpK N); exact mul_le_mul_of_nonneg_left (by linarith [Nat.cast_nonneg (α:=ℝ) (Pn c N)]) (by unfold polyBound; positivity)
