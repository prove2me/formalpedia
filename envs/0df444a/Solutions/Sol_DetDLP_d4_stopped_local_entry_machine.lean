-- Prove2me | solution 1 for DetDLP.d4_stopped_local_entry_machine
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T08:50:01.649715+00:00
-- url     : https://prove2.me/submissions/b878c1f2-0c9a-42f0-9c26-5c75a96d2fb4

import Theorems.Thm_DetDLP_d4_residue_lift_eq
import Definitions.Def_DetDLP_D4StoppedNode
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_DetDLP_W5_M6Sort
import Theorems.Thm_DetDLP_d4b_three_oracle_mux
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Polynomial DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle DetDLP.D4StoppedNode
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open Groundwork DetDLP_W1_Queries
attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.const PolyT.id' P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_cond__4c673073da15 P2M_Groundwork_PolyT_ite__226169acf219 PolyT.optionElim PolyT.flatMap PolyT.map first_poly more_poly w5_M6Sort.decode_poly w5_M6Sort.encode_poly frame_poly

private abbrev Scan := Bool × Bool × Bits × List Bits
private def scanStep (s : Scan) (b : Bool) : Scan :=
  bif s.1 then bif s.2.1 then s else (false,true,b :: s.2.2.1,s.2.2.2)
  else bif s.2.1 then bif b then (true,false,s.2.2.1,s.2.2.2)
    else (false,false,[],s.2.2.1.reverse :: s.2.2.2)
  else bif b then (false,true,[],s.2.2.2) else (true,true,[],s.2.2.2)
private def rows (w : Bits) : List Bits := (w.foldl scanStep (false,false,[],[])).2.2.2.reverse
@[local fun_prop] private theorem rows_poly : PolyT rows := by
  have h : PolyT fun w : Bits => w.foldl scanStep (false,false,[],[]) := by
    refine PolyT.foldl_add (g := fun _ => scanStep) (by fun_prop) (by fun_prop) (by unfold scanStep; fun_prop) ?_
    refine ⟨fun _ => 4,PB.const 4,?_⟩
    rintro w ⟨k,j,u,l⟩ b _
    cases k <;> cases j <;> cases b <;> simp [scanStep,len_pair,len_bools,len_bool,len_cons,len_nil] <;> omega
  unfold rows; fun_prop
private theorem scanFrame (u rev : Bits) (l : List Bits) :
    (Encoding.frame u).foldl scanStep (false,true,rev,l) = (false,false,[],(rev.reverse ++ u) :: l) := by
  induction u generalizing rev with
  | nil => simp [Encoding.frame,scanStep]
  | cons b u ih => simpa [Encoding.frame,List.foldl,scanStep] using ih (b::rev)
private theorem scanRows {α : Type} (f : α → Bits) (xs : List α) (l : List Bits) :
    (Encoding.encodeList f xs).foldl scanStep (false,false,[],l) = (true,true,[],(xs.map f).reverse ++ l) := by
  induction xs generalizing l with
  | nil => rfl
  | cons a xs ih =>
    change (Encoding.frame (f a) ++ Encoding.encodeList f xs).foldl scanStep (false,true,[],l) = _
    rw [List.foldl_append,scanFrame]; simpa using ih (f a :: l)
@[simp] private theorem rowsEnc {α : Type} (f : α → Bits) (xs : List α) : rows (Encoding.encodeList f xs) = xs.map f := by simp [rows,scanRows]

private def getRow (w : Bits) := (rows (second (third (first w)))).getD (PolyT.bval (second w)) []
private def oracleQuery (w : Bits) : Bits :=
  let row := getRow w
  let d := third (first w)
  bif row.headD false then true :: false :: Encoding.encodeList id [row.tail,third w]
  else false :: encodePortQuery (first d) (PolyT.bval (first row.tail))
    ((rows (second row.tail)).map fun r =>
      (bif r.headD false then third d else third w).getD (PolyT.bval r.tail) false)
private theorem pairEnc (a b : Bits) : Encoding.encodeList id [a,b] = true :: (frame a ++ true :: (frame b ++ [false])) := by simp [Encoding.encodeList]
private theorem triEnc (a b c : Bits) : Encoding.encodeList id [a,b,c] = triple a b c := by simp [Encoding.encodeList,triple]
@[local fun_prop] private theorem rowPoly : PolyT getRow := by unfold getRow third second; fun_prop
@[local fun_prop] private theorem sndPoly {α : Type} [Enc α] {f : α → Bits} (h : PolyT f) : PolyT (fun x => second (f x)) := first_poly (more_poly h)
@[local fun_prop] private theorem thdPoly {α : Type} [Enc α] {f : α → Bits} (h : PolyT f) : PolyT (fun x => third (f x)) := sndPoly (more_poly h)
@[local fun_prop] private theorem encPairP {α : Type} [Enc α] {a b : α → Bits} (ha : PolyT a) (hb : PolyT b) : PolyT (fun x => Encoding.encodeList id [a x,b x]) := by simp only [pairEnc]; fun_prop
@[local fun_prop] private theorem encTriP {α : Type} [Enc α] {a b c : α → Bits} (ha : PolyT a) (hb : PolyT b) (hc : PolyT c) : PolyT (fun x => Encoding.encodeList id [a x,b x,c x]) := by simp only [triEnc,triple]; fun_prop
private theorem queryPoly : PolyT oracleQuery := by
  have pp : PolyT (fun w : Bits => (rows (second (getRow w).tail)).map fun r => (bif r.headD false then third (third (first w)) else third w).getD (PolyT.bval r.tail) false) := by
    apply PolyT.map <;> fun_prop
  unfold oracleQuery encodePortQuery
  dsimp only
  apply P2M_Groundwork_PolyT_cond__4c673073da15
  · exact PolyT.headD rowPoly (PolyT.const _)
  · apply P2M_Groundwork_PolyT_cons__3a60f43a3b86 (PolyT.const _)
    apply P2M_Groundwork_PolyT_cons__3a60f43a3b86 (PolyT.const _)
    exact encPairP (PolyT.tail rowPoly) (thdPoly PolyT.id')
  · apply P2M_Groundwork_PolyT_cons__3a60f43a3b86 (PolyT.const _)
    apply encTriP
    · fun_prop
    · apply w5_M6Sort.cw_poly; fun_prop
    · exact pp

private def finish (w : Bits) : Bits :=
  let u := first w; let ans := second w
  let coeff := second (first u)
  bif (getRow u).headD false then ans else
    encodeNatListBin ((w5_M6Sort.decode ans).flatMap fun v =>
      if coeff.isEmpty then [] else v :: coeff.tail.map (fun _ => 0))
private theorem finishPoly : PolyT finish := by unfold finish second; fun_prop

private theorem rowSpec {origG G : Graph} {f : ℤ[X]} {l P deg : ℕ} (s : StoppedSpec origG G f l P deg)
    (o : Bits) (d : ℕ) (α : Fin deg → Bool) (w : Fin G.nV) (β : Fin (G.deg w) → Bool) :
    getRow (encodePortQuery (D3Stopped.descOf d f (s.payload o α)) w.val (List.ofFn β)) = (s.vTable w).bits := by
  simp [getRow,encodePortQuery,D3Stopped.descOf,StoppedSpec.payload,StoppedSpec.tableBits,third,second,List.getD_eq_getElem?_getD]

private theorem routeSpec (perm : List (Bool × ℕ)) (a b : Bits) :
    ((rows (Encoding.encodeList (fun r : Bool × ℕ => r.1 :: countWord r.2) perm)).map fun r =>
      (bif r.headD false then a else b).getD (PolyT.bval r.tail) false) = routedBits perm a b := by
  simp only [rowsEnc,List.map_map,routedBits]
  apply List.map_congr_left
  rintro ⟨t,n⟩ _; cases t <;> simp [List.getD_eq_getElem?_getD]

private theorem finishOrig (u r fb : Bits) (a : List ℕ) (h : (getRow u).headD false = false)
    (hf : second (first u) = fb) (hr : r = encodeNatListBin a) :
    finish (Encoding.encodeList id [u,r]) = encodeNatListBin (pad fb.length a) := by
  simp only [finish,second,first_cons,more_cons,id_eq,h,hr,Bool.cond_false,w5_M6Sort.decode_encode]
  change encodeNatListBin _ = encodeNatListBin _
  rw [show first (more (first u)) = fb from hf]
  cases fb <;> simp [pad,List.map_const']

private def natPoly (k n : ℕ) := k * (n+1)^k
private theorem natPolyPB (k : ℕ) : PB (natPoly k) := ⟨k, fun _ => le_rfl⟩
private theorem natPoly_mono (k : ℕ) {a b : ℕ} (h : a ≤ b) : natPoly k a ≤ natPoly k b := by unfold natPoly; gcongr
private theorem pbCast (k n : ℕ) : (natPoly k n : ℝ) = polyBound k n := by simp [natPoly,polyBound]

private theorem dispatchMachine (E F : PrimitiveMachine) (oE : Fin E.tapeCount) (oF : Fin F.tapeCount) (c : ℕ) :
    ∃ (L : PrimitiveMachine) (oL : Fin L.tapeCount) (k : ℕ), ∀ (n : ℕ) (u x ans : Bits) (j : Fin 2)
      (τ : ℝ), 1 ≤ τ → u.length ≤ natPoly c n → x.length ≤ natPoly c n → ans.length ≤ natPoly c n →
      oracleQuery u = (if j = 0 then false :: x else true :: false :: x) →
      (if j = 0 then RunsWithin E oE x ans τ (polyBound c n) else RunsWithin F oF x ans τ (polyBound c n)) →
      RunsWithin L oL u (finish (Encoding.encodeList id [u,ans])) (polyBound k n * τ) (polyBound k n) := by
  let A : Fin 3 → PrimitiveMachine := ![E,F,F]
  let o : (j : Fin 3) → Fin (A j).tapeCount := Fin.cons oE (Fin.cons oF (Fin.cons oF (fun i => Fin.elim0 i)))
  obtain ⟨mux,m,hm⟩ := DetDLP.d4b_three_oracle_mux A o
  obtain ⟨pre,op,a,hpre⟩ := PolyTBridge.polyT_listBool_runsWithin _ queryPoly
  obtain ⟨post,ofin,b,hpost⟩ := PolyTBridge.polyT_listBool_runsWithin _ finishPoly
  let preMux := DetDLP_W1_Pipeline.WordPipeline.machine pre op mux
  let saved := DetDLP_W1_SavedCall.savedCall preMux (DetDLP_W1_Pipeline.WordPipeline.resultPort pre op mux mux.inputTape)
  let M := DetDLP_W1_Pipeline.WordPipeline.machine saved (DetDLP_W1_SavedCall.dest preMux) post
  let pairLen := fun n => 4*natPoly c n+5
  let lin := fun n => 100*(preMux.tapeCount+10)*(pairLen n+10)
  let fixed := pre.tapeCount + mux.tapeCount + post.tapeCount + saved.tapeCount + 10
  let budget := fun n => natPoly a (natPoly c n) + m*(natPoly c n+natPoly c n+2) + lin n + natPoly b (pairLen n) + fixed
  have p := natPolyPB c
  have pp : PB pairLen := ((PB.const 4).mul p).add (PB.const 5)
  have pl : PB lin := (PB.const (100*(preMux.tapeCount+10))).mul (pp.add (PB.const 10))
  have pb : PB budget := (((((natPolyPB a).comp p).add ((PB.const m).mul ((p.add p).add (PB.const 2)))).add pl).add ((natPolyPB b).comp pp)).add (PB.const fixed)
  obtain ⟨k,hk⟩ := pb
  refine ⟨M,DetDLP_W1_Pipeline.WordPipeline.resultPort saved (DetDLP_W1_SavedCall.dest preMux) post ofin,k,?_⟩
  intro n u x ans j τ ht hu hx hans htag hrun
  have hxrun : RunsWithin mux mux.inputTape (oracleQuery u) ans (m * (τ + x.length + 1)) (m * (polyBound c n + x.length + 1)) := by
    rw [htag]; fin_cases j
    · exact hm 0 x ans _ _ hrun
    · exact hm 1 x ans _ _ hrun
  have main := DetDLP_W1_Pipeline.WordPipeline.run pre op mux mux.inputTape (hpre u) hxrun
  have keep := DetDLP_W1_SavedCall.savedCall_run preMux _ main
  have out := DetDLP_W1_Pipeline.WordPipeline.run saved (DetDLP_W1_SavedCall.dest preMux) post ofin keep (hpost _)
  apply PolyTBridge.runsWithin_mono_local out
  all_goals
    have flen (z : Bits) : (Encoding.frame z).length = 2*z.length+1 := by induction z <;> simp_all [Encoding.frame] <;> omega
    have hpLen : (Encoding.encodeList id [u,ans]).length ≤ pairLen n := by simp [Encoding.encodeList,flen,pairLen]; omega
    have hcost : DetDLP_W1_SavedCall.extraTime u ans ≤ lin n ∧ DetDLP_W1_SavedCall.extraSpace preMux u ans ≤ lin n := by
      simp only [DetDLP_W1_SavedCall.extraTime,DetDLP_W1_SavedCall.extraSpace,DetDLP_W1_SavedCall.preSteps,DetDLP_W1_SavedCall.postSteps,lin]
      have ha' : u.length ≤ pairLen n := by dsimp only [pairLen]; omega
      have hb' : ans.length ≤ pairLen n := by dsimp only [pairLen]; omega
      generalize preMux.tapeCount = tapes
      constructor <;> nlinarith only [ha',hb',hpLen,Nat.mul_le_mul_left tapes ha',Nat.mul_le_mul_left tapes hb',Nat.mul_le_mul_left tapes hpLen]
    have ca := natPoly_mono a hu; have cb := natPoly_mono b hpLen
    have hc := hk n
    have cz : (budget n : ℝ) ≤ polyBound k n := by rw [←pbCast]; exact_mod_cast hc
    change _ ≤ _
    simp only [budget,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at cz
    have H1 : polyBound a u.length ≤ (natPoly a (natPoly c n) : ℝ) := by rw [←pbCast]; exact_mod_cast ca
    have H2 : polyBound b (Encoding.encodeList id [u,ans]).length ≤ (natPoly b (pairLen n) : ℝ) := by rw [←pbCast]; exact_mod_cast cb
    have H3 : (DetDLP_W1_SavedCall.extraTime u ans : ℝ) ≤ (lin n : ℝ) := by exact_mod_cast hcost.1
    have H4 : (DetDLP_W1_SavedCall.extraSpace preMux u ans : ℝ) ≤ (lin n : ℝ) := by exact_mod_cast hcost.2
    have HM := mul_le_mul_of_nonneg_left (show (x.length : ℝ) ≤ (natPoly c n : ℝ) by exact_mod_cast hx) (Nat.cast_nonneg (α:=ℝ) m)
    have HF : (fixed : ℝ) = pre.tapeCount + (mux.tapeCount:ℝ) + post.tapeCount + saved.tapeCount + 10 := by simp [fixed]
  · have hpos : 0 ≤ (budget n : ℝ) - m := by
      dsimp [budget]; push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) (natPoly a (natPoly c n)),Nat.cast_nonneg (α:=ℝ) (lin n),Nat.cast_nonneg (α:=ℝ) (natPoly b (pairLen n)),Nat.cast_nonneg (α:=ℝ) fixed, mul_nonneg (Nat.cast_nonneg (α:=ℝ) m) (Nat.cast_nonneg (α:=ℝ) (natPoly c n))]
    have HH := mul_nonneg hpos (sub_nonneg.mpr ht)
    simp only [budget,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at HH
    nlinarith [mul_nonneg (sub_nonneg.mpr cz) (show 0 ≤ τ by linarith),mul_nonneg (Nat.cast_nonneg (α:=ℝ) m) (Nat.cast_nonneg (α:=ℝ) (natPoly c n)),Nat.cast_nonneg (α:=ℝ) fixed]
  · rw [←pbCast c n]; nlinarith
theorem solution (E F : PrimitiveMachine) (oE : Fin E.tapeCount) (oF : Fin F.tapeCount) (c : ℕ) :
    ∃ (L : PrimitiveMachine) (oL : Fin L.tapeCount) (k : ℕ),
    ∀ (S P l d deg : ℕ) (origDesc : Bits) (origG G : Graph) (f : ℤ[X]) (hf : f.Monic)
      (s : StoppedSpec origG G f l P deg) (A : Tensor origG (Fin l → ℕ))
      (α : Fin deg → Bool) (To Tp : ℕ),
      let payload := s.payload origDesc α
      let n := S+payload.length
      let desc := D3Stopped.descOf d f payload
      1 ≤ To → 1 ≤ Tp → (∀ v t j, A v t j < 2^P) →
      (∀ (w : Fin G.nV) (β : Fin (G.deg w) → Bool), (encodePortQuery desc w.val (List.ofFn β)).length ≤ c*(n+1)^c) →
      (∀ v t, let inp := encodePortQuery origDesc v.val (List.ofFn t)
              let ans := encodeNatListBin (List.ofFn (A v t))
              inp.length ≤ c*(n+1)^c ∧ ans.length ≤ c*(n+1)^c ∧ RunsWithin E oE inp ans To (polyBound c n)) →
      (∀ w pkt (h : s.vTable w = .pkt pkt) β, let p := s.packet w pkt h
              let inp := Encoding.encodeList id [pkt,List.ofFn β]
              let ans := residue f l p.creation hf (p.entry β)
              inp.length ≤ c*(n+1)^c ∧ ans.length ≤ c*(n+1)^c ∧ RunsWithin F oF inp ans Tp (polyBound c n)) →
      ∀ w β, RunsWithin L oL (encodePortQuery desc w.val (List.ofFn β)) (residue f l P hf (s.entry hf A α w β))
        (polyBound k n * (To + (Tp : ℝ))) (polyBound k n) := by
  obtain ⟨L,o,k,H⟩ := dispatchMachine E F oE oF c
  refine ⟨L,o,k,?_⟩
  intro S P l d deg origDesc origG G f hf s A α To Tp payload n desc hTo hTp hA hin hO hP w β
  let u := encodePortQuery desc w.val (List.ofFn β)
  have hr := rowSpec s origDesc d α w β
  change getRow u = _ at hr
  have hfb : second (first u) = polynomialBits f := by simp [u,desc,encodePortQuery,D3Stopped.descOf,second]
  have htime : (1:ℝ) ≤ To + (Tp:ℝ) := by exact_mod_cast (show 1 ≤ To+Tp by omega)
  cases hh : s.vTable w with
  | orig v perm =>
    let i : Fin origG.nV := ⟨v,(s.validOrig w v perm hh).choose⟩
    let raw := routedBits perm (List.ofFn α) (List.ofFn β)
    let t : Fin (origG.deg i) → Bool := fun j => raw[j.val]?.getD false
    have htlen : raw.length = origG.deg i := by simpa [raw,routedBits,i] using (s.validOrig w v perm hh).choose_spec.1
    have ht : List.ofFn t = raw := by
      apply List.ext_getElem
      · simp [htlen]
      · intro j h₁ h₂; simp [t,h₂]
    let x := encodePortQuery origDesc v (List.ofFn t)
    let ans := encodeNatListBin (List.ofFn (A i t))
    obtain ⟨hx,ha,run⟩ := hO i t
    have htag : oracleQuery u = false :: x := by
      simp only [oracleQuery,hr,hh,VertexSpec.bits,List.headD_cons,Bool.cond_false,List.tail_cons]
      simp only [u,desc,payload,encodePortQuery,D3Stopped.descOf,StoppedSpec.payload,third,second,first_cons,more_cons,id_eq,List.tail_cons,decode_count,x,ht,routeSpec,raw]
    have main := H n u x ans 0 _ htime (hin w β) hx ha htag (PolyTBridge.runsWithin_mono_local run (by linarith [Nat.cast_nonneg (α:=ℝ) Tp] : (To:ℝ) ≤ To+Tp) le_rfl)
    have hv : s.entry hf A α w β = liftBase f l P (A i t) := by
      unfold StoppedSpec.entry; split <;> rename_i he <;> cases (he.symm.trans hh) <;> rfl
    rw [hv,(d4_residue_lift_eq f l P P hf le_rfl).2 _ (hA i t)]
    have he := finishOrig u ans (polynomialBits f) _ (by simp [hr,hh,VertexSpec.bits]) hfb (rfl : ans = _)
    simpa only [he,polynomialBits,List.length_ofFn] using main
  | pkt pkt =>
    let p := s.packet w pkt hh
    let x := Encoding.encodeList id [pkt,List.ofFn β]
    let ans := residue f l p.creation hf (p.entry β)
    obtain ⟨hx,ha,run⟩ := hP w pkt hh β
    have htag : oracleQuery u = true :: false :: x := by
      simp only [oracleQuery,hr,hh,VertexSpec.bits,List.headD_cons,Bool.cond_true,List.tail_cons]
      simp [u,encodePortQuery,third,second,x]
    have main := H n u x ans 1 _ htime (hin w β) hx ha htag (PolyTBridge.runsWithin_mono_local run (by linarith [Nat.cast_nonneg (α:=ℝ) To] : (Tp:ℝ) ≤ To+Tp) le_rfl)
    have hv : s.entry hf A α w β = lift hf P (p.entry β) := by
      unfold StoppedSpec.entry; split <;> rename_i he <;> cases (he.symm.trans hh) <;> rfl
    rw [hv,(d4_residue_lift_eq f l p.creation P hf p.le_precision).1]
    simpa only [finish,second,first_cons,more_cons,id_eq,hr,hh,VertexSpec.bits,List.headD_cons,Bool.cond_true] using main
