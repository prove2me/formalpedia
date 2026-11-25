-- Prove2me | solution 1 for DetDLP.d4_outer_dispatch
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T09:16:28.491805+00:00
-- url     : https://prove2.me/submissions/77b66920-f368-448d-b7ff-2ff72c149a3b

import Theorems.Thm_DetDLP_d4_residue_lift_eq
import Theorems.Thm_DetDLP_d4b_three_oracle_mux
import Definitions.Def_DetDLP_D4StoppedNode
import Definitions.Def_DetDLP_W5_M6Sort
import Definitions.Def_ToTuring_Lib_List2
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace DetDLP.D4StoppedNode.SourceWords
open Polynomial AppendixD4 OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open Groundwork DetDLP_W1_Queries
attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.const PolyT.id' P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_cond__4c673073da15 P2M_Groundwork_PolyT_ite__226169acf219 PolyT.optionElim PolyT.flatMap PolyT.map first_poly more_poly w5_M6Sort.decode_poly w5_M6Sort.encode_poly frame_poly

private def field : ℕ → Bits → Bits
  | 0 => first
  | n+1 => fun w => field n (more w)
@[local fun_prop] private theorem fieldPoly {α : Type} [Enc α] (i : ℕ) {f : α → Bits} (h : PolyT f) : PolyT fun w => field i (f w) := by
  induction i generalizing α with
  | zero => exact first_poly h
  | succ i ih => exact ih (more_poly h)
private theorem encFlat (xs : List Bits) : Encoding.encodeList id xs = xs.flatMap (fun z => true :: frame z) ++ [false] := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp [Encoding.encodeList,ih]
@[local fun_prop] private theorem encPoly {α : Type} [Enc α] {xs : α → List Bits} (h : PolyT xs) : PolyT fun w => Encoding.encodeList id (xs w) := by simp_rw [encFlat]; fun_prop

/-- A lookup sends the original descriptor and restored original index to E. A stopped query
    sends a canonical BTN instance to the continuation with the open assignment in its payload. -/
def prepare (w : Bits) : Bits :=
  let src := first w; let fields := src.tail; let alpha := field 2 w
  bif src.headD false then
    let d := field 4 fields; let payload := field 2 d
    let pin := Encoding.encodeList id [field 0 payload,field 1 payload,alpha]
    let desc := Encoding.encodeList id [field 0 d,field 1 d,pin]
    true :: false :: Encoding.encodeList id [desc,field 3 fields,field 0 fields,field 2 fields,field 1 fields]
  else false :: Encoding.encodeList id [field 0 fields,field 1 fields,alpha]

theorem preparePoly : PolyT prepare := by
  unfold prepare
  dsimp only
  apply P2M_Groundwork_PolyT_cond__4c673073da15
  · exact PolyT.headD (first_poly PolyT.id') (PolyT.const _)
  · apply P2M_Groundwork_PolyT_cons__3a60f43a3b86 (PolyT.const _)
    apply P2M_Groundwork_PolyT_cons__3a60f43a3b86 (PolyT.const _)
    apply encPoly
    fun_prop (disch:=assumption)
  · apply P2M_Groundwork_PolyT_cons__3a60f43a3b86 (PolyT.const _)
    apply encPoly
    fun_prop

theorem prepareLookup (o : Bits) (v κ l q i : ℕ) (a : Bits) :
    prepare (encodePortQuery (lookupDesc o v κ l q) i a) = false :: encodePortQuery o v a := by
  simp [prepare,field,lookupDesc,encodePortQuery]

theorem prepareStopped (o : Bits) (S l P d i : ℕ) (f : ℤ[X]) (G : Graph) (table a : Bits) :
    prepare (encodePortQuery (stoppedDesc o S l P d f G table) i a) = true :: false ::
      encodeBTNInstance (D3Stopped.descOf d f (Encoding.encodeList id [o,table,a])) G S P l := by
  simp [prepare,field,stoppedDesc,D3Stopped.descOf,encodePortQuery,encodeBTNInstance]

/-- Bounded width is constructed from the full saved query, not merely the binary count field. -/
def finish (w : Bits) : Bits :=
  let u := field 0 w; let reply := field 1 w; let src := field 0 u
  bif src.headD false then reply else
    let fuel := u.take (PolyT.bval (field 2 src.tail))
    encodeNatListBin ((w5_M6Sort.decode reply).flatMap fun a =>
      if fuel.isEmpty then [] else a :: fuel.tail.map (fun _ => 0))

theorem finishPoly : PolyT finish := by
  unfold finish
  fun_prop

theorem finishStopped (u ans : Bits) (hu : (first u).headD false = true) :
    finish (Encoding.encodeList id [u,ans]) = ans := by simp only [finish,field,first_cons,more_cons,id_eq,hu,Bool.cond_true]

theorem finishLookup (o : Bits) (v κ l q i : ℕ) (b : Bits) (a : List ℕ)
    (h : κ ≤ (encodePortQuery (lookupDesc o v κ l q) i b).length) :
    finish (Encoding.encodeList id [encodePortQuery (lookupDesc o v κ l q) i b,encodeNatListBin a]) = encodeNatListBin (pad κ a) := by
  let u := encodePortQuery (lookupDesc o v κ l q) i b
  have src : first u = lookupDesc o v κ l q := by simp [u,encodePortQuery]
  have deg : PolyT.bval (field 2 (lookupDesc o v κ l q).tail) = κ := by simp [lookupDesc,field]
  change finish (Encoding.encodeList id [u,_]) = _
  simp only [finish,field,first_cons,more_cons,id_eq,src,lookupDesc,List.headD_cons,Bool.cond_false,List.tail_cons,decode_count,w5_M6Sort.decode_encode]
  have hu : (u.take κ).length = κ := by simpa [u] using (Nat.min_eq_left h)
  generalize hh : u.take κ = width at hu ⊢
  subst κ
  cases width <;> simp [pad,List.map_const']
end DetDLP.D4StoppedNode.SourceWords
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace DetDLP.D4StoppedNode
open Polynomial AppendixD4 ResidualScalarOracle OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open Groundwork
private def natPoly (k n : ℕ) := k * (n+1)^k
private theorem natPolyPB (k : ℕ) : PB (natPoly k) := ⟨k, fun _ => le_rfl⟩
private theorem natPoly_mono (k : ℕ) {a b : ℕ} (h : a ≤ b) : natPoly k a ≤ natPoly k b := by unfold natPoly; gcongr
private theorem pbCast (k n : ℕ) : (natPoly k n : ℝ) = polyBound k n := by simp [natPoly,polyBound]

private theorem dispatchMachine (E F : PrimitiveMachine) (oE : Fin E.tapeCount) (oF : Fin F.tapeCount) (c : ℕ) :
    ∃ (L : PrimitiveMachine) (oL : Fin L.tapeCount) (k : ℕ), ∀ (n : ℕ) (u x ans : Bits) (j : Fin 2)
      (τ : ℝ), 1 ≤ τ → u.length ≤ natPoly c n → x.length ≤ natPoly c n → ans.length ≤ natPoly c n →
      SourceWords.prepare u = (if j = 0 then false :: x else true :: false :: x) →
      (if j = 0 then RunsWithin E oE x ans τ (polyBound c n) else RunsWithin F oF x ans τ (polyBound c n)) →
      RunsWithin L oL u (SourceWords.finish (Encoding.encodeList id [u,ans])) (polyBound k n * τ) (polyBound k n) := by
  let A : Fin 3 → PrimitiveMachine := ![E,F,F]
  let o : (j : Fin 3) → Fin (A j).tapeCount := Fin.cons oE (Fin.cons oF (Fin.cons oF (fun i => Fin.elim0 i)))
  obtain ⟨mux,m,hm⟩ := DetDLP.d4b_three_oracle_mux A o
  obtain ⟨pre,op,a,hpre⟩ := PolyTBridge.polyT_listBool_runsWithin _ SourceWords.preparePoly
  obtain ⟨post,ofin,b,hpost⟩ := PolyTBridge.polyT_listBool_runsWithin _ SourceWords.finishPoly
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
  have hxrun : RunsWithin mux mux.inputTape (SourceWords.prepare u) ans (m * (τ + x.length + 1)) (m * (polyBound c n + x.length + 1)) := by
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

/-- One physical dispatcher for both concrete source descriptors. Supplies polynomial overhead
    for any certified call time; the continuation consumes only the pinned BTN query below. -/
theorem sourceDispatch (E A : PrimitiveMachine) (oE : Fin E.tapeCount) (oA : Fin A.tapeCount) (c : ℕ) :
    ∃ (B : PrimitiveMachine) (ob : Fin B.tapeCount) (k : ℕ),
    (∀ (n i v κ l q : ℕ) (origDesc β : Bits) (f : ℤ[X]) (hf : f.Monic) (a : Fin l → ℕ) (τ : ℝ),
      let u := encodePortQuery (lookupDesc origDesc v κ l q) i β
      let x := encodePortQuery origDesc v β
      let ans := encodeNatListBin (List.ofFn a)
      κ = f.natDegree → κ ≤ u.length → 1 ≤ τ → (∀ j, a j < 2^q) →
      u.length ≤ c*(n+1)^c → x.length ≤ c*(n+1)^c → ans.length ≤ c*(n+1)^c →
      RunsWithin E oE x ans τ (polyBound c n) →
      RunsWithin B ob u (residue f l q hf (liftBase f l q a)) (polyBound k n * τ) (polyBound k n)) ∧
    (∀ (n i S P q l d deg : ℕ) (origDesc : Bits) (origG G : Graph) (f : ℤ[X]) (hf : f.Monic)
      (s : StoppedSpec origG G f l P deg) (V : Tensor origG (Fin l → ℕ)) (α : Fin deg → Bool) (τ : ℝ),
      let u := encodePortQuery (stoppedDesc origDesc S l P d f G s.tableBits) i (List.ofFn α)
      let x := encodeBTNInstance (D3Stopped.descOf d f (s.payload origDesc α)) G S P l
      let ans := residue f l P hf (BTNContract G (s.entry hf V α))
      P ≤ q → 1 ≤ τ → u.length ≤ c*(n+1)^c → x.length ≤ c*(n+1)^c → ans.length ≤ c*(n+1)^c →
      RunsWithin A oA x ans τ (polyBound c n) →
      RunsWithin B ob u (residue f l q hf (s.value hf V q α)) (polyBound k n * τ) (polyBound k n)) := by
  obtain ⟨B,ob,k,H⟩ := dispatchMachine E A oE oA c
  refine ⟨B,ob,k,?_,?_⟩
  · intro n i v κ l q o β f hf a τ u x ans hd hκ ht ha hu hx hans hrun
    have main := H n u x ans 0 τ ht hu hx hans (SourceWords.prepareLookup ..) hrun
    rw [(d4_residue_lift_eq f l q q hf le_rfl).2 a ha, ← hd]
    exact (SourceWords.finishLookup o v κ l q i β (List.ofFn a) hκ) ▸ main
  · intro n i S P q l d deg o origG G f hf s V α τ u x ans hpq ht hu hx hans hrun
    have main := H n u x ans 1 τ ht hu hx hans (SourceWords.prepareStopped ..) hrun
    have tag : (DetDLP_W1_Queries.first u).headD false = true := by simp [u,encodePortQuery,stoppedDesc]
    rw [StoppedSpec.value,(d4_residue_lift_eq f l P q hf hpq).1]
    rw [SourceWords.finishStopped u ans tag] at main
    exact main
end DetDLP.D4StoppedNode

open Polynomial DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle DetDLP.D4StoppedNode OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
theorem solution (E A : PrimitiveMachine) (oE : Fin E.tapeCount) (oA : Fin A.tapeCount) (c : ℕ) :
    ∃ (B : PrimitiveMachine) (ob : Fin B.tapeCount) (k : ℕ),
    (∀ (n i v κ l q : ℕ) (origDesc β : Bits) (f : ℤ[X]) (hf : f.Monic) (a : Fin l → ℕ) (τ : ℝ),
      let u := encodePortQuery (lookupDesc origDesc v κ l q) i β
      let x := encodePortQuery origDesc v β
      let ans := encodeNatListBin (List.ofFn a)
      κ = f.natDegree → κ ≤ u.length → 1 ≤ τ → (∀ j, a j < 2^q) →
      u.length ≤ c*(n+1)^c → x.length ≤ c*(n+1)^c → ans.length ≤ c*(n+1)^c →
      RunsWithin E oE x ans τ (polyBound c n) →
      RunsWithin B ob u (residue f l q hf (liftBase f l q a)) (polyBound k n * τ) (polyBound k n)) ∧
    (∀ (n i S P q l d deg : ℕ) (origDesc : Bits) (origG G : Graph) (f : ℤ[X]) (hf : f.Monic)
      (s : StoppedSpec origG G f l P deg) (V : Tensor origG (Fin l → ℕ)) (α : Fin deg → Bool) (τ : ℝ),
      let u := encodePortQuery (stoppedDesc origDesc S l P d f G s.tableBits) i (List.ofFn α)
      let x := encodeBTNInstance (D3Stopped.descOf d f (s.payload origDesc α)) G S P l
      let ans := residue f l P hf (BTNContract G (s.entry hf V α))
      P ≤ q → 1 ≤ τ → u.length ≤ c*(n+1)^c → x.length ≤ c*(n+1)^c → ans.length ≤ c*(n+1)^c →
      RunsWithin A oA x ans τ (polyBound c n) →
      RunsWithin B ob u (residue f l q hf (s.value hf V q α)) (polyBound k n * τ) (polyBound k n)) := by
  exact DetDLP.D4StoppedNode.sourceDispatch E A oE oA c
