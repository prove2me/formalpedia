-- Prove2me | solution 1 for DetDLP.fp_native_uniform_wiring
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T11:15:36.14112+00:00
-- url     : https://prove2.me/submissions/71a27862-2f38-46a0-9af6-e357168a07ec

import Theorems.Thm_DetDLP_w3_m5_modmul_r2
import Theorems.Thm_DetDLP_M3A_FpWireCore_native_core_family
import Theorems.Thm_DetDLP_M3A_FpPolyDefs_fpBuild_poly
import Theorems.Thm_DetDLP_M3A_FpPolyDefs_fpEntry_poly
import Theorems.Thm_DetDLP_M3A_FpPolyDefs_fpEntry_ordinary_vertex
import Theorems.Thm_DetDLP_M3A_FpPolyDefs_fpEntry_lookup_vertex_v2

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DetDLP.M3A.FpPolyDefs
open S8J S8H.PointAddresses S8L.FpPair.Address S8G.FpMoment S8L.FpPair S8L.FpPair.Stage.Links w4_M5PortTensor S8C FpSlotTile
attribute [-simp] Fin.natAdd_eq_addNat
variable {D M K : ℕ} (hd : 1 ≤ D)
private theorem spl {a : Code} {A : w3_FactorLayout} {n : ℕ} {l r : Fin n → Fin A.nb} {L R : ℕ → ℕ} (ha : Models a A)
    (hl : ∀ u, L u.val = (l u).val) (hr : ∀ u, R u.val=(r u).val) : Models (splice a n L R) (links A l r) := by
  refine ⟨congrArg (·+n) ha.ng,ha.nb,congrArg (·+(n+n)) ha.ne,?_,?_⟩
  all_goals intro e;induction e using Fin.addCases with
    | left u => simp [splice,links,splitMap,ha.ne,u.isLt,ha.gate,ha.bit]
    | right u => induction u using Fin.addCases with
      | left u => simp [splice,links,splitMap,ha.ne,ha.ng,u.isLt,hl]
      | right u => simp [splice,links,splitMap,ha.ne,ha.ng,hr]
private theorem out_val (i : Fin (2*D)) : w4_M5EdgeNat.edgeBase D 9 i.val = (ext hd (outPos i)).val := by unfold ext;rw [ext_outPos];rfl
private theorem input_val (b : Bool) (i : Fin D) : (ext hd (inPos b i)).val = (if b then D+i.val else i.val) := by unfold ext;rw [ext_inPos];cases b <;> change _ + D*_ = _ <;> simp [tag,Nat.add_comm]
private theorem addr_val (i : Fin (2*D)) (l : Fin 4) : addrN D i.val l.val=(addr hd i l).val := by simp only [addrN,(mul_spec hd).nb,addr,Fin.val_natAdd,AddLayout.reg];change _ = (_+_)+(4*i.val+l.val);ring
private theorem linked_model : Models (linked D) (Stage.Links.layout hd) := by
  unfold linked;rw [show 4*D=2*D+2*D by omega]; apply spl (stage_spec hd)
  · intro e;induction e using Fin.addCases with
    | left u => simpa [left,u.isLt] using addr_val hd u 0
    | right u => simpa [left] using addr_val hd u 2
  · intro e;induction e using Fin.addCases with
    | left u => simp only [right,Fin.addCases_left,Fin.val_castAdd,if_pos u.isLt];rw [out_val hd,(mul_spec hd).nb];rfl
    | right u => simp [right,out_val hd];rfl
private theorem stage_model : Models (stage D) (FpArithNet.boundedStage hd) := by
  apply spl (sum_spec (linked_model hd) (add_spec _))
  · intro i; simp only [(linked_model hd).nb,FpArithNet.stageOut,Fin.val_natAdd,AddLayout.reg,Fin.val_castSucc,Fin.val_zero,Nat.add_zero]
  · intro i;exact addr_val hd ⟨i.val,by omega⟩ 1
private theorem x_val (i : Fin D) : xPort D i.val = (xBits (k:=K) hd i).val := by
  change (linked D).nb +4*(D+1+i.val)+2 = (S8L.FpPair.Stage.Links.layout hd).nb+(4*((finProdFinEquiv ((1:Fin 8),i.castSucc)).val)+2)
  rw [(linked_model hd).nb]; simp [finProdFinEquiv_apply_val];omega
private theorem z_val (i : Fin K) : zPort D+i.val=(zBits hd i).val := by
  rw [zPort,(linked_model hd).nb];change _ = ((Stage.Links.layout hd).nb+8*(D+1)*4)+i.val; rfl
private theorem base_model : Models (base M D K) (FpArithNet.base hd M K) := sum_spec (repeat_spec (slot_models hd) _) (sum_spec (repeat_spec (stage_model hd) _) (repeat_spec (stage_model hd) _))
private theorem slot_val (s : Fin (4*M)) (u : Fin (slotLayout D K hd).nb) : s.val*(slot D K).nb+u.val=(FpArithNet.slotPort hd s u).val := by unfold slot;rw [(slot_models hd).nb];simp [FpArithNet.slotPort,finProdFinEquiv_apply_val];ring
private theorem stage_val (b : Bool) (s : Fin (2*M)) (u : Fin (FpArithNet.boundedStage hd).nb) :
    sPort M D K ((if b then 2*M else 0)+s.val) u.val = (FpArithNet.stagePort (k:=K) hd b s u).val := by
  cases b <;> simp [sPort,FpArithNet.stagePort,tiles,finProdFinEquiv_apply_val,slot,(slot_models hd).nb,(stage_model hd).nb] <;> ring
private theorem out_bus (j : Fin D) : (linked D).nb+4*j.val=(FpArithNet.stageOut hd j).val := by rw [(linked_model hd).nb];simp [FpArithNet.stageOut,AddLayout.reg]
private theorem op_bus (b : Bool) (j : Fin D) : (if b then D+j.val else j.val)=(FpArithNet.operand hd b j).val := (input_val hd b j).symm
private theorem sides (s : Fin (4*M)) : s.val/(2*M) = (if FpArithNet.whichSide s then 1 else 0) ∧ s.val=(if FpArithNet.whichSide s then 2*M else 0)+(FpArithNet.whichStep s).val := by
  have hpos : 0 < 2*M := by have := s.isLt;omega
  have hlt : s.val/(2*M)<2 := (Nat.div_lt_iff_lt_mul hpos).mpr (by omega)
  have H := Nat.mod_add_div s.val (2*M)
  by_cases h : s.val<2*M
  · simp [FpArithNet.whichSide,FpArithNet.whichStep,h.not_ge,Nat.div_eq_of_lt h,Nat.mod_eq_of_lt h]
  · have he : s.val/(2*M)=1 := by have := (Nat.le_div_iff_mul_le hpos).mpr (by simpa using Nat.le_of_not_gt h : 1*(2*M) ≤ s.val);omega
    simp [FpArithNet.whichSide,FpArithNet.whichStep,Nat.le_of_not_gt h,he];rw [he] at H; omega
private theorem tie_model (b : Bool) (e : Fin ((4*M)*D+(4*M)*D)) :
    tie b M D K e.val = (if b then (FpArithNet.ties (k:=K) hd e).2 else (FpArithNet.ties hd e).1).val := by
  induction e using Fin.addCases with
  | left u => obtain ⟨⟨s,j⟩,rfl⟩ := finProdFinEquiv.surjective u
              have he := (finProdFinEquiv (s,j)).isLt
              have div := congrArg (fun v : Fin (4*M) × Fin D => v.1.val) (finProdFinEquiv.symm_apply_apply (s,j))
              have mod := congrArg (fun v : Fin (4*M) × Fin D => v.2.val) (finProdFinEquiv.symm_apply_apply (s,j))
              change (finProdFinEquiv (s,j)).val/D=s.val at div; change (finProdFinEquiv (s,j)).val%D=j.val at mod
              simp only [FpArithNet.ties,Fin.addCases_left,FpArithNet.factorTie,Equiv.symm_apply_apply,tie,Fin.val_castAdd,if_pos he,div,mod]
              cases b
              · exact (congrArg (s.val*(slot D K).nb+·) (x_val (K:=K) hd j)).trans (slot_val hd s _)
              · simp only [if_true];rw [← stage_val,← (sides s).2];exact congrArg _ (op_bus hd true j)
  | right u => obtain ⟨⟨s,j⟩,rfl⟩ := finProdFinEquiv.surjective u
               have div := congrArg (fun v : Fin (4*M) × Fin D => v.1.val) (finProdFinEquiv.symm_apply_apply (s,j))
               have mod := congrArg (fun v : Fin (4*M) × Fin D => v.2.val) (finProdFinEquiv.symm_apply_apply (s,j))
               change (finProdFinEquiv (s,j)).val/D=s.val at div;change (finProdFinEquiv (s,j)).val%D=j.val at mod
               simp only [tie,Fin.val_natAdd,Nat.not_lt_of_ge (Nat.le_add_right ..),if_false,Nat.add_sub_cancel_left,div,mod,FpArithNet.ties,Fin.addCases_right,FpArithNet.chainTie,Equiv.symm_apply_apply]
               have side := (sides s).2; rw [(sides s).1]; change s.val=(if FpArithNet.whichSide s then 2*M else 0)+s.val%(2*M) at side
               by_cases h : s.val%(2*M)=0 <;> simp only [FpArithNet.whichStep,h,if_pos] <;> cases b <;> cases eq : FpArithNet.whichSide s <;>
                 simp only [eq,Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true,Nat.zero_mul,Nat.one_mul,Nat.zero_add,Nat.sub_self,Nat.sub_zero,← stage_val,← out_bus,← op_bus] at side ⊢ <;>
                 first | rfl | (congr 1 <;> omega)
private theorem chain_model : Models (chains M D K) (FpArithNet.chains hd M K) := by unfold chains;rw [show 2*(4*M*D)=4*M*D+4*M*D by omega];exact spl (base_model hd) (tie_model hd false) (tie_model hd true)

private theorem prefix_model (u : Fin (4*M*D)) : prefixAddr M D K u.val=(FpArithNet.prefixPort (k:=K) hd u).val := by
  obtain ⟨⟨s,j⟩,rfl⟩ := finProdFinEquiv.surjective u
  have div := congrArg (fun v : Fin (4*M) × Fin D => v.1.val) (finProdFinEquiv.symm_apply_apply (s,j))
  have mod := congrArg (fun v : Fin (4*M) × Fin D => v.2.val) (finProdFinEquiv.symm_apply_apply (s,j))
  change (finProdFinEquiv (s,j)).val/D=s.val at div;change (finProdFinEquiv (s,j)).val%D=j.val at mod
  simp only [FpArithNet.prefixPort,Equiv.symm_apply_apply,prefixAddr,div,mod,← slot_val,← x_val]
private theorem arith_model (pre : List Bool) : Models (arith M D K pre.length) (FpArithNet.arith hd M K pre) := by
  apply spl (sum_spec (chain_model hd) (S8H0.AnchoredLayout.anchorModels _))
  · intro i;exact prefix_model hd (Fin.castLE (min_le_right ..) i)
  · intro i;change (chains M D K).nb+i.val=(FpArithNet.chains hd M K).nb+i.val;rw [(chain_model hd).nb]
theorem layout_models (pre : List Bool) : Models (whole M D K pre.length) (FpArithNet.layout hd M K pre) := by
  apply M3B.ECLayout.models _ _ (arith_model hd pre);intro i j; change _=(FpArithNet.slotPort hd i (zBits hd j)).val
  rw [← slot_val,← z_val];omega

end DetDLP.M3A.FpPolyDefs
end

section
set_option autoImplicit false
open DetDLP DetDLP.M3A DetDLP.M3A.FpPolyDefs DetDLP.w4_M5Network

namespace DetDLP.M3A.LightEntries

private theorem indicator_spec (P n : ℕ) (hp : 0 < P) (hn : 0 < n) (b : Bool) :
    EncodesTruncPoly P n (indicator n b) (if b then 1 else 0) := by
  classical
  let c (i : Fin n) := if i.val = 0 then b.toNat else 0
  refine ⟨c, ?_, ?_, ?_⟩
  · have h : 1 < 2^P := Nat.one_lt_pow (by omega) (by decide)
    intro i; cases b <;> simp [c]; split <;> omega
  · unfold indicator
    congr 1
    rw [List.ofFn_eq_map, show List.range n = (List.finRange n).map Fin.val by simp, List.map_map]; rfl
  · cases b with
    | false => simp [truncPolyOfCoeffs,c]
    | true =>
      let z : Fin n := ⟨0,hn⟩
      unfold truncPolyOfCoeffs
      rw [Finset.sum_eq_single z]
      · simp [z,c,Polynomial.monomial_zero_left]
      · intro i _ h; have hi : i.val ≠ 0 := fun e => h (Fin.ext e); simp [c,hi]
      · simp

private theorem equal_ports (G : WireGraph) (e : Fin G.nE)
    (a : Fin (G.subdivision.deg (G.equalityVertex e)) → Bool) :
    equal (List.ofFn a) = decide (a (G.equalityLeftPort e) = a (G.equalityRightPort e)) := by
  let l := G.equalityLeftPort e
  let r := G.equalityRightPort e
  have ex (i : Fin (G.subdivision.deg (G.equalityVertex e))) : i = l ∨ i = r := by
    have h := (G.mem_equalityPorts_iff e _).mp (List.get_mem (G.subdivision.ports _) i)
    have nd := G.subdivision_ports_nodup (G.equalityVertex e)
    exact h.imp (fun t => nd.get_inj_iff.mp (t.trans (G.get_equalityLeftPort e).symm))
      (fun t => nd.get_inj_iff.mp (t.trans (G.get_equalityRightPort e).symm))
  have hn : 0 < G.subdivision.deg (G.equalityVertex e) := by simp
  let z : Fin (G.subdivision.deg (G.equalityVertex e)) := ⟨0,hn⟩
  have hz : bit (List.ofFn a) 0 = a z := by
    simp [bit,List.getD_eq_getElem?_getD,z]; congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [equal,hz,List.all_eq_true,List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff,
    beq_iff_eq,decide_eq_true_eq]
  constructor
  · intro h; exact (h l).trans (h r).symm
  · intro h i; rcases ex i with rfl|rfl <;> rcases ex z with h'|h' <;> rw [h'] <;> first | rfl | exact h | exact h.symm

theorem fpEquality (w : W) (P : ℕ) (hp : 0 < P)
    (G : WireGraph) (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P (len w))
    (hng : (whole (m w) (d w) (k w) (pre w).length).ng ≤ G.nV) (e : Fin G.nE)
    (a : Fin (G.subdivision.deg (G.equalityVertex e)) → Bool) :
    EncodesTruncPoly P (len w) (fpEntry (encodePortQuery w (G.equalityVertex e).val (List.ofFn a)))
      (w3_liftTensor G T (G.equalityVertex e) a) := by
  let c := whole (m w) (d w) (k w) (pre w).length
  change c.ng ≤ G.nV at hng
  have h : ¬ G.nV+e.val < c.ng := by omega
  have h' : ¬ G.nV+e.val < c.ng-4*m w := by omega
  simp [fpEntry,encodePortQuery,DetDLP_W1_Queries.second,DetDLP_W1_Queries.third,
    ← show c = whole (m w) (d w) (k w) (pre w).length from rfl,
    h,h',w3_liftTensor,WireGraph.equalityVertex,Fin.addCases_right]
  change EncodesTruncPoly P (len w) (indicator (len w) (equal (List.ofFn a))) _
  rw [equal_ports G e a]
  have H := indicator_spec P (len w) hp (Nat.zero_lt_succ _)
    (decide (a (G.equalityLeftPort e) = a (G.equalityRightPort e)))
  simpa only [decide_eq_true_eq] using H

end DetDLP.M3A.LightEntries
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open DetDLP DetDLP.M3A DetDLP.M3A.FpPolyDefs DetDLP.w4_M5Network

namespace DetDLP.M3A.LightEntries

attribute [-simp] Fin.natAdd_eq_addNat
private theorem equal_ref {n : ℕ} (a : Fin n → Bool) (r : Fin n) :
    equal (List.ofFn a) = true ↔ ∀ i, a i = a r := by
  let z : Fin n := ⟨0,by have := r.isLt; omega⟩
  have hz : bit (List.ofFn a) 0 = a z := by simp [bit,List.getD_eq_getElem?_getD,show 0<n from z.isLt,z]
  simp only [equal,hz,List.all_eq_true,List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff,beq_iff_eq]
  exact ⟨fun h i => (h i).trans (h r).symm, fun h i => (h i).trans (h z).symm⟩
private theorem bit_port_agreement (A : w3_FactorLayout) (T : w3_factorTest A) (b : Fin A.nb) (a) :
    let G := w3_factorGraph A; let v := Fin.natAdd A.ng b
    equal (List.ofFn a) = G.subdivisionTensor (w3_factorChecks A T) (G.oldVertex v) a := by
  let G := w3_factorGraph A; let v := Fin.natAdd A.ng b
  let idx (e : {i : Fin A.ne // A.bit i = b}) := G.portIndex v e.val (w3_bitInc A b e.val e.property)
  let r := idx ⟨A.rep b,A.rep_bit b⟩
  apply Bool.eq_iff_iff.mpr
  rw [equal_ref a (G.oldPort v r),G.subdivisionTensor_oldVertex (w3_factorChecks A T) v a]
  simp only [v,w3_factorChecks,Fin.addCases_right,decide_eq_true_eq]
  constructor
  · exact fun h e => h _
  · intro h i
    obtain ⟨j,rfl⟩ := (G.oldPort_bijective v).surjective i
    let e := (G.ports v).get j
    have he := (G.mem_ports v e).mp (List.get_mem _ j)
    have hb : A.bit e = b := by
      rcases he with he|he <;> have hh := congrArg Fin.val he
      · change (A.gate e).val = A.ng + b.val at hh; have := (A.gate e).isLt; omega
      · apply Fin.ext; change A.ng + (A.bit e).val = A.ng + b.val at hh; omega
    have hj : idx ⟨e,hb⟩ = j := (G.ports_nodup v).get_inj_iff.mp (G.get_portIndex v e _)
    exact hj ▸ h ⟨e,hb⟩

theorem fpBit (q : w3_Query) (w : W)
    (hP : 0 < w3_precision q) (hn : len w = w3_len q) (A : w3_FactorLayout)
    (hg : (whole (m w) (d w) (k w) (pre w).length).ng ≤ A.ng)
    {n : ℕ} (s : Fin A.ng ≃ (w3_lookupSlot q ⊕ Fin n)) (test : w3_factorTest A)
    (addr : (v : Fin (w3_factorGraph A).nV) → (Fin ((w3_factorGraph A).deg v) → Bool) → ℕ)
    (b : Fin A.nb) (a : Fin ((w3_factorGraph A).subdivision.deg ((w3_factorGraph A).oldVertex (Fin.natAdd A.ng b))) → Bool) :
    let G := w3_factorGraph A; let v := G.oldVertex (Fin.natAdd A.ng b)
    EncodesTruncPoly (w3_precision q) (w3_len q) (fpEntry (encodePortQuery w v.val (List.ofFn a)))
      (w3_liftTensor G (w3_gateWeight (w3_incSlot A s) addr (w3_factorChecks A test)) v a) := by
  let G := w3_factorGraph A; let v := Fin.natAdd A.ng b
  have check : equal (List.ofFn a) = w3_factorChecks A test v (fun j => a (G.oldPort v j)) := by
    exact (bit_port_agreement A test b a).trans (G.subdivisionTensor_oldVertex _ v a)
  have slot : w3_incSlot A s v = .inr (Fin.natAdd n b) := by
    unfold w3_incSlot
    simp only [Equiv.trans_apply,v]
    erw [finSumFinEquiv_symm_apply_natAdd]; rfl
  let c := whole (m w) (d w) (k w) (pre w).length
  change c.ng ≤ A.ng at hg
  have h : ¬ A.ng+b.val < c.ng := by omega
  have h' : ¬ A.ng+b.val < c.ng-4*m w := by omega
  have entry : fpEntry (encodePortQuery w (G.oldVertex v).val (List.ofFn a)) = indicator (len w) (equal (List.ofFn a)) := by
    change fpEntry (encodePortQuery w (A.ng+b.val) (List.ofFn a)) = _
    simp [fpEntry,encodePortQuery,DetDLP_W1_Queries.second,DetDLP_W1_Queries.third,WireGraph.oldVertex,
      ← show c = whole (m w) (d w) (k w) (pre w).length from rfl,h,h']
  dsimp only
  rw [entry]
  have lift : w3_liftTensor G (w3_gateWeight (w3_incSlot A s) addr (w3_factorChecks A test)) (G.oldVertex v) a =
      (if equal (List.ofFn a) then 1 else 0) := by
    unfold w3_liftTensor WireGraph.oldVertex
    erw [Fin.addCases_left]
    unfold w3_gateWeight; erw [slot]; rw [check]
  rw [lift]
  have H := indicator_spec (w3_precision q) (len w) hP (Nat.zero_lt_succ _) (equal (List.ofFn a))
  rw [hn] at H
  simpa only [hn] using H

end DetDLP.M3A.LightEntries
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace DetDLP.M3A.Witness
open FpPolyDefs FpWireCore OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

noncomputable def input {p m M : ℕ} [Fact p.Prime] (F : Fin m → List (ZMod p)ˣ) (seed : FpSeed p m)
    (P : (ZMod p)ˣ) (T : ℕ) (y : w3_Label M (w3_fpFB F).totalCoords) (η : W) :=
  Encoding.encodeList id [encodeNatListBin [p,(P : ZMod p).val,M,T],
    encodeNatListBin ((List.finRange m).flatMap fun i => [(seed i).1.val+1,(seed i).2.val]),
    encodeFpFactorBlocks F,encodeNatListBin (List.ofFn fun j => (y j).val),η]

private theorem encode_map {α β : Type} (f : β → W) (g : α → β) (xs : List α) :
    Encoding.encodeList (f ∘ g) xs = Encoding.encodeList f (xs.map g) := by
  induction xs <;> simp_all [Encoding.encodeList]

private theorem fields_map {α : Type} (f : α → W) (xs : List α) :
    fld (Encoding.encodeList f xs) = xs.map f := by
  rw [show Encoding.encodeList f xs = Encoding.encodeList id (xs.map f) from encode_map id f xs]
  exact m89_enum_words.fields_encode _

private theorem width_eq (n : ℕ) : width n=Nat.clog 2 n := by
  unfold width;rw [Nat.size_eq_bits_len];apply le_antisymm
  · apply Nat.size_le.mpr;cases n with
    | zero => decide
    | succ n => simpa using Nat.le_pow_clog (by decide : 1<2) (n+1)
  · apply Nat.clog_le_of_le_pow;have := Nat.lt_size_self (n-1);omega

private theorem pair_get {α : Type} (a b : α → ℕ) (l : List α) (i : ℕ) (hi : i < l.length) (s : Fin 2) :
    (l.flatMap fun t => [a t,b t]).getD (2*i+s.val) 0 = (if s=0 then a l[i] else b l[i]) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons t ts ih => cases i with
    | zero => fin_cases s <;> rfl
    | succ i => simpa [Nat.mul_succ,show 2*i+2+s.val=(2*i+s.val+1)+1 by omega] using ih i (by simpa using hi)

theorem prefix_sum {m : ℕ} (f : Fin m → ℕ) (i : Fin m) :
    ((List.ofFn f).take i.val).sum = ∑ j ∈ Finset.univ.filter (fun j : Fin m => j < i), f j := by
  let xs := (List.finRange m).take i.val
  have he : xs.toFinset = Finset.univ.filter (fun j : Fin m => j < i) := by
    ext j
    simp only [List.mem_toFinset,Finset.mem_filter,Finset.mem_univ,true_and]
    change j ∈ (List.finRange m).take i.val ↔ j.val < i.val
    rw [List.mem_take_iff_idxOf_lt (List.mem_finRange j),List.idxOf_finRange]
  rw [List.ofFn_eq_map,←List.map_take,←he]
  exact (List.sum_toFinset f (List.nodup_finRange m).take).symm

variable {p m M : ℕ} [Fact p.Prime] (F : Fin m → List (ZMod p)ˣ) (seed : FpSeed p m)
    (P : (ZMod p)ˣ) (T : ℕ) (y : w3_Label M (w3_fpFB F).totalCoords) (η : W)
local notation "w" => input F seed P T y η
local notation "Q" => native F seed P η

theorem input_meta (nz : NeZero M) :
    let q := Q nz y w (bitLen p) (Nat.clog 2 (2*T))
    FpPolyDefs.m w=m ∧ d w=q.b ∧ k w=q.k ∧ pre w=η ∧ prime w=p ∧ threshold w=T ∧
      target w=(P : ZMod p).val ∧ prec w=w3_precision q ∧ len w=w3_len q ∧
      sizeField w=budget m q.b q.k (w3_precision q) := by
  let q := Q nz y w (bitLen p) (Nat.clog 2 (2*T))
  have hm : FpPolyDefs.m w=m := by simp [FpPolyDefs.m,field,input,fld,m89_enum_words.fields_encode,
    encodeFpFactorBlocks,show ∀ (g : List (ZMod p)ˣ → W) xs, m89_enum_words.fields (Encoding.encodeList g xs)=xs.map g from fields_map]
  have h : prime w=p ∧ threshold w=T ∧ groupSize w=M ∧ pre w=η ∧ target w=(P : ZMod p).val := by
    simp [input,field,prime,threshold,groupSize,num,nums,pre,target,fld]
  obtain ⟨hp,ht,hm0,he,hP⟩ := h
  have hb : d w=bitLen p := by rw [d,hp,width_eq];rfl
  have hk : k w=Nat.clog 2 (2*T) := by rw [k,ht,width_eq]
  have hpr : prec w=w3_precision q := by rw [prec,hm,hk,hm0,width_eq];rfl
  refine ⟨hm,hb,hk,he,hp,ht,hP,hpr,?_,?_⟩
  · rw [len,hm];rfl
  · rw [sizeField,hm,hb,hk,hpr];rfl

theorem seed_fields (i : Fin m) :
    (nums (field w 1)).getD (2*i.val) 0=(seed i).1.val+1 ∧
    (nums (field w 1)).getD (2*i.val+1) 0=(seed i).2.val := by
  have h (s : Fin 2) := pair_get (fun j => (seed j).1.val+1) (fun j => (seed j).2.val) (List.finRange m) i.val
    (by simp) s
  have hi : (List.finRange m)[i.val] = i := by ext; simp
  simp only [input,field,nums,fld,m89_enum_words.fields_encode,List.getD_cons_succ,List.getD_cons_zero,
    w5_M6Sort.decode_encode]
  constructor
  · simpa only [Fin.val_zero,Nat.add_zero,if_true,hi] using h 0
  · simpa only [Fin.val_one,if_neg (by decide : (1 : Fin 2) ≠ 0),hi] using h 1

theorem blocks_fields :
    blocks w = List.ofFn (fun i => (F i).map fun v : (ZMod p)ˣ => (v : ZMod p).val) := by
  simp only [blocks,field,input,fld,m89_enum_words.fields_encode,List.getD_cons_succ,List.getD_cons_zero]
  rw [encodeFpFactorBlocks,show ∀ (g : List (ZMod p)ˣ → W) xs, m89_enum_words.fields (Encoding.encodeList g xs)=xs.map g from fields_map,
    List.map_map,List.map_ofFn]
  congr 1
  funext i
  change nums (Encoding.encodeList (fun v : (ZMod p)ˣ => countWord (v : ZMod p).val) (F i)) = _
  rw [show Encoding.encodeList (fun v : (ZMod p)ˣ => countWord (v : ZMod p).val) (F i) =
      encodeNatListBin ((F i).map fun v : (ZMod p)ˣ => (v : ZMod p).val) from
        encode_map countWord (fun v : (ZMod p)ˣ => (v : ZMod p).val) (F i)]
  exact w5_M6Sort.decode_encode _

theorem lookup_fields (i : Fin m) :
    let xs := (blocks w).getD i.val []
    xs.length=((w3_fpFB F).blocks i).length ∧
      ∀ r : Fin ((w3_fpFB F).blocks i).length,
        xs.getD r.val 0=((((w3_fpFB F).blocks i).get r).toMul : ZMod p).val ∧
        num (field w 3) ((((blocks w).take i.val).map List.length).sum+r.val) =
          (y ((w3_fpFB F).coordOf i r)).val := by
  rw [blocks_fields]
  have hx : (List.ofFn (fun i => (F i).map fun v : (ZMod p)ˣ => (v : ZMod p).val)).getD i.val [] =
      (F i).map fun v : (ZMod p)ˣ => (v : ZMod p).val := by simp [List.getD_eq_getElem?_getD,i.isLt]
  dsimp only
  rw [hx]
  constructor
  · simp [w3_fpFB]
  intro r
  have hr : r.val<(F i).length := by simpa [w3_fpFB] using r.isLt
  constructor
  · simp [List.getD_eq_getElem?_getD,hr,w3_fpFB,List.get_eq_getElem]
  · have hoff : (((List.ofFn (fun i => (F i).map fun v : (ZMod p)ˣ => (v : ZMod p).val)).take i.val).map List.length).sum =
        (w3_fpFB F).blockOffset i := by
      rw [List.map_take,List.map_ofFn]
      simpa [IndexedFactorBase.blockOffset,w3_fpFB,Function.comp_def] using prefix_sum (fun j => (F j).length) i
    rw [hoff]
    simp only [num,field,input,nums,fld,m89_enum_words.fields_encode,List.getD_cons_succ,List.getD_cons_zero,
      w5_M6Sort.decode_encode]
    change (List.ofFn (fun j => (y j).val)).getD ((w3_fpFB F).coordOf i r).val 0 = _
    exact (show ∀ {n : ℕ} (f : Fin n → ℕ) (i : Fin n), (List.ofFn f).getD i.val 0=f i by
      intro n f i; simp [List.getD_eq_getElem?_getD,i.isLt]) _ _

end DetDLP.M3A.Witness
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace DetDLP.M3A.Witness

open FpArithNet FpWireCore w4_MulParams w4_M5GraphBounds w4_M5Network
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem gate_budget {d : ℕ} (hd : 1 ≤ d) (m k : ℕ) (η : List Bool) (prec : ℕ) :
    (FpArithNet.layout hd m k η).ng ≤ budget m d k prec := by
  let u := (w3_fpMulLayout d hd).ng
  have hu : u ≤ 256*(d+1) := by
    have h₁ := J_lt_linear hd
    have h₂ := n0_upper hd
    have h₃ := L_le_half_J hd
    have h₄ := L1_le_L d
    have h₅ := L2_le_L d
    change vertexCount d ≤ _
    unfold vertexCount
    rw [Nat.mul_comm (L2 _) (L1 _),L1_mul_L2]
    omega
  let S := FpSlotTile.slotLayout d k hd
  let B := boundedStage hd
  let np := min η.length (4*m*d)
  have hg : S.ng=u+u+2*d+(2*d+2*d)+8*(d+1)+(3*d+5*(d+1))+k+min k (d+1) := rfl
  have hb : B.ng=(u+u+2*d+(2*d+2*d))+(d+1)+d := rfl
  change (4*m*S.ng+(2*m*B.ng+2*m*B.ng))+(4*m*d+4*m*d)+(np+1)+np+4*m ≤ _
  rw [hg,hb,budget]
  have hn : np ≤ 4*m*d := min_le_right .. 
  nlinarith only [Nat.mul_le_mul_left m hu,Nat.mul_le_mul_left m (min_le_left k (d+1)),hn]

theorem input_bounds {d : ℕ} (hd : 1 ≤ d) (m k : ℕ) (η : List Bool) (prec : ℕ)
    (desc : List Bool) :
    let L := FpArithNet.layout hd m k η
    let G := (w3_factorGraph L).subdivision
    let S := budget m d k prec
    G.nV ≤ (S+desc.length+1)^5 ∧ ∀ (v : Fin G.nV) (a : Fin (G.deg v) → Bool),
      (encodePortQuery desc v.val (List.ofFn a)).length+1 ≤ (S+desc.length+1)^5 := by
  let L := FpArithNet.layout hd m k η
  let G := (w3_factorGraph L).subdivision
  let S := budget m d k prec
  let B := S+desc.length+1
  have hs : 1≤S := by unfold S budget; omega
  have he : 2*L.ne ≤ S := by
    have := FpArithNet.edge_budget (m:=m) (k:=k) hd η
    change L.ne ≤ _ at this
    unfold S budget;omega
  have hb : L.nb ≤ L.ne := by simpa using Fintype.card_le_of_injective L.rep (Function.RightInverse.injective L.rep_bit)
  have hg : L.ng ≤ S := gate_budget hd m k η prec
  have hv : G.nV ≤ 2*S := by change L.ng+L.nb+L.ne ≤ _;omega
  have hB : 2 ≤ B := by dsimp [B];omega
  have hp : 16*B ≤ B^5 := by
    rw [show (5:ℕ)=4+1 by decide,pow_succ]
    exact Nat.mul_le_mul_right B (show 2^4 ≤ B^4 from Nat.pow_le_pow_left hB 4)
  constructor
  · exact hv.trans ((show 2*S ≤ 16*B by dsimp [B];omega).trans hp)
  · intro v a
    have hv' : v.val < G.nV := v.isLt
    have hc := w3_queryIndexLength v.val
    have hdg : G.deg v ≤ G.nE := (List.length_filter_le ..).trans List.length_finRange.le
    have hne : G.nE = 2*L.ne := WireGraph.subdivision_nE _
    rw [w3_queryExactLength,List.length_ofFn]
    apply le_trans _ hp
    change 2*(desc.length+(countWord v.val).length+G.deg v)+7+1 ≤ 16*(S+desc.length+1)
    omega

end DetDLP.M3A.Witness
end

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option backward.isDefEq.respectTransparency false
namespace DetDLP.M3A.Witness
open FpPolyDefs
open S8H.PointAddresses S8H.WirePacket S8J FpArithNet FpWireCore S8G.FpMoment
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
attribute [-simp] Fin.natAdd_eq_addNat
variable {p M D K T m' : ℕ} [Fact p.Prime] (F : Fin m' → List (ZMod p)ˣ) (seed : FpSeed p m') (P : (ZMod p)ˣ) (η : W) (nz : NeZero M) (y : w3_Label M (w3_fpFB F).totalCoords) (w : W) (hd : 1 ≤ D)
local notation "Q" => native F seed P η nz y w D K
local notation "A" => FpArithNet.arith hd m' K η
local notation "B" => FpArithNet.bus (m:=m') (k:=K) hd η
local notation "L" => FpArithNet.layout hd m' K η
local notation "G" => w3_factorGraph L
local notation "sl" => M3B.ECLayout.gateSlots (q:=Q) A B (numbering m')
private theorem mask_iff (v : Fin (G).subdivision.nV) : v ∈ (w3_incLookups L sl).image (G).oldVertex ↔ (A).ng ≤ v.val ∧ v.val < (L).ng := by
  constructor
  · intro h; obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp h;obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hu
    change (A).ng ≤ (A).ng+(FpChainBijection.row t.2.2 t.1 t.2.1).val ∧ (A).ng+_ < (A).ng+4*m'; have := (FpChainBijection.row t.2.2 t.1 t.2.1).isLt;omega
  · rintro ⟨lo,hi⟩; let s : Fin (4*m') := ⟨v.val-(A).ng,by change v.val < (A).ng+4*m' at hi;omega⟩;obtain ⟨b,i,j,e⟩ := FpChainBijection.row_surj s
    let u := M3B.ECLayout.vertex A B (FpChainBijection.row b i j); apply Finset.mem_image.mpr; refine ⟨u,Finset.mem_image.mpr ⟨(i,j,b),Finset.mem_univ _,rfl⟩,?_⟩
    apply Fin.ext;change (A).ng+(FpChainBijection.row b i j).val = v.val;rw [e];dsimp [s];omega

theorem packet_of_fields (hw : m w=m' ∧ d w=D ∧ k w=K ∧ pre w=η ∧ prec w=w3_precision Q ∧ len w=w3_len Q)
    (Z : w3_WireCore Q 1000000) (hZ : NativeCore (T:=T) F seed P η nz y w hd Z) : fpBuild w=w3_wirePacket Z := by
  obtain ⟨hm,hD,hK,hp,hq,hl⟩ := hw;obtain ⟨hdesc,hS,hG,hL,_⟩ := hZ
  have model := layout_models (M:=m') (K:=K) hd η
  let c := whole m' D K η.length
  have graph : packet (c.ng+c.nb) c.ne c.gate (fun e => c.ng+c.bit e) = (G).subdivision.encode := by
    rw [show c.ng+c.nb=(G).nV from congrArg₂ (·+·) model.ng model.nb,show c.ne=(G).nE from model.ne]
    apply packet_eq; exact model.gate;intro i; exact congrArg₂ (·+·) model.ng (model.bit i)
  have ng : (arith m' D K η.length).ng=(A).ng := by have h := model.ng;change _+4*m'=(A).ng+4*m' at h;omega
  unfold fpBuild sizeField;rw [hm,hD,hK,hp,hq,hl];change Encoding.encodeList id [w,packet (c.ng+c.nb) c.ne c.gate _,_,_,_,_,_,_,_] = _;rw [graph]
  unfold w3_wirePacket encodeTerminalBTNInstance; rw [hdesc,hS]; cases Z with | mk ZG ZL ZS ZD ZT ZC ZE Zlive Zdead Zcount Zdeg Zorient Zedges Zdegrees Zeq Zshape =>
    change ZG = G at hG; subst ZG; have hset := eq_of_heq hL; change ZL = w3_incLookups L sl at hset;subst ZL
    simp only [model.ng,model.nb,model.ne,ng];congr 2
    have rr (n : ℕ) : List.range n = (List.finRange n).map Fin.val := by simp
    rw [List.ofFn_eq_map,rr,List.map_map]
    have hmask : (List.finRange (G).subdivision.nV).map ((fun n : ℕ => decide ((A).ng ≤ n ∧ n < (L).ng)) ∘ Fin.val) = (List.finRange (G).subdivision.nV).map (fun v => decide (v ∈ (w3_incLookups L sl).image (G).oldVertex)) := by
      apply List.map_congr_left;intro v _;apply Bool.eq_iff_iff.mpr; simpa only [Function.comp_apply,decide_eq_true_eq] using (mask_iff F seed P η nz y w hd v).symm
    exact congrArg (fun l : W => [(G).subdivision.encode,countWord D,countWord m',countWord K,countWord (budget m' D K (w3_precision Q)),countWord (w3_precision Q),countWord (w3_len Q),l]) hmask

end DetDLP.M3A.Witness
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace DetDLP.M3A.Witness
open FpPolyDefs FpWireCore S8H.PointAddresses S8J FpArithNet FpChainBijection w4_M5Network
open M3B.ECLayout (vertex port gateSlots)
attribute [-simp] Fin.natAdd_eq_addNat
variable {p m M T : ℕ} [Fact p.Prime]

theorem address_at (A : w3_FactorLayout) {n k : ℕ} (f : Fin n → Fin k → Fin A.nb) (i : Fin n) (x) :
    address A f (vertex A f i) x = bitsToNat (fun j => x (port A f i j)) := by
  let h : ∃ l, vertex A f i=vertex A f l := ⟨i,rfl⟩
  rw [address,dif_pos h]; have e : i=h.choose := Fin.natAdd_injective _ _ (Fin.castAdd_injective _ _ h.choose_spec)
  have aux (l : Fin n) (el : i=l) (ev : vertex A f i=vertex A f l) : (bitsToNat fun j => x (ev.symm ▸ port A f l j)) = bitsToNat (fun j => x (port A f i j)) := by subst l; rfl
  exact aux _ e h.choose_spec

theorem hash_injective (seed : FpSeed p m) (F : Fin m → List (ZMod p)ˣ) (i : Fin m) (hn : (F i).Nodup) :
    Function.Injective (fun r => w3_fpHashWord seed i (w3_fpResidue (((w3_fpFB F).blocks i).get r).toMul).val) := by
  intro u v h; let a := (seed i).1.val+1
  have ha : a < p := by have := (seed i).1.isLt; dsimp [a]; omega
  have hz : (a : ZMod p) ≠ 0 := by intro h; have eq := congrArg ZMod.val h; rw [ZMod.val_natCast_of_lt ha,ZMod.val_zero] at eq; dsimp [a] at eq; omega
  let val (r : Fin ((w3_fpFB F).blocks i).length) := (((w3_fpFB F).blocks i).get r).toMul
  have hx : (a : ZMod p)*(val u : ZMod p)+(seed i).2.val = (a : ZMod p)*(val v : ZMod p)+(seed i).2.val := by
    change (a*(val u : ZMod p).val+(seed i).2.val)%p=(a*(val v : ZMod p).val+(seed i).2.val)%p at h
    have hc := congrArg (fun n : ℕ => (n : ZMod p)) h
    simpa only [ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul,ZMod.natCast_val,ZMod.cast_id] using hc
  have hu : val u=val v := Units.ext (mul_left_cancel₀ hz (add_right_cancel hx))
  exact ((hn.map Additive.ofMul.injective).get_inj_iff).mp (congrArg Additive.ofMul hu)


private theorem eq_edge {p n : ℕ} (w : W) (h : len w=n) (hp : 0<p) (G : WireGraph)
    (t : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly p n)
    (hg : (whole (FpPolyDefs.m w) (d w) (k w) (pre w).length).ng ≤ G.nV) (e : Fin G.nE)
    (a : Fin (G.subdivision.deg (G.equalityVertex e)) → Bool) :
    EncodesTruncPoly p n (fpEntry (encodePortQuery w (G.equalityVertex e).val (List.ofFn a)))
      (w3_liftTensor G t (G.equalityVertex e) a) := by
  subst n
  exact LightEntries.fpEquality w p hp G t hg e a

variable (F : Fin m → List (ZMod p)ˣ) (seed : FpSeed p m)
  (P : (ZMod p)ˣ) (T : ℕ) (nz : NeZero M) (y : w3_Label M (w3_fpFB F).totalCoords)
  (η : List Bool) (hd : 1 ≤ bitLen p)
local notation "D" => bitLen p
local notation "K" => Nat.clog 2 (2*T)
local notation "w" => input F seed P T y η
local notation "Q" => native F seed P η nz y w D K
local notation "A" => FpArithNet.arith hd m K η
local notation "B" => FpArithNet.bus (m:=m) (k:=K) hd η
local notation "L" => FpArithNet.layout hd m K η
local notation "G" => w3_factorGraph L
local notation "sl" => gateSlots (q:=Q) A B (numbering m)
local notation "t" => FpArithNet.arithTest (k:=K) hd p T (ZMod.val (P : ZMod p)) seed η
local notation "tL" => FpArithNet.test (k:=K) hd p T (ZMod.val (P : ZMod p)) seed η
local notation "adr" => address A B
local notation "wt" => w3_gateWeight (w3_incSlot L sl) adr (w3_factorChecks L tL)

theorem native_entries (hF : ∀ i, (F i).Nodup) (v : Fin (G).subdivision.nV)
    (a : Fin ((G).subdivision.deg v) → Bool) :
    EncodesTruncPoly (w3_precision Q) (w3_len Q) (fpEntry (encodePortQuery w v.val (List.ofFn a)))
      (w3_liftTensor G wt v a) := by
  obtain ⟨hm,hdw,hkw,hη,hpr,hth,htg,hp,hl,_⟩ := input_meta F seed P T y η nz
  have hp0 : 0<w3_precision Q := by unfold w3_precision; omega
  have hc : (whole (FpPolyDefs.m w) (d w) (k w) (pre w).length).ng=(L).ng := by
    rw [hm,hdw,hkw,hη]
    exact (layout_models hd η).ng
  induction v using Fin.addCases with
  | right e =>
    have hg : (L).ng ≤ (G).nV := Nat.le_add_right _ _
    exact eq_edge w hl hp0 G wt (hc.le.trans hg) e a
  | left v =>
    induction v using Fin.addCases with
    | right b => exact LightEntries.fpBit Q w hp0 hl L hc.le sl tL adr b a
    | left gate =>
      induction gate using Fin.addCases with
      | left g =>
        apply fpEntry_ordinary_vertex hd Q w η (P : ZMod p).val seed sl adr hp0 hm hdw hkw hη hpr hth htg hl _ _ g a
        · intro i
          obtain ⟨h₁,h₂⟩ := seed_fields F seed P T y η i
          exact ⟨by rw [h₁];omega,h₂⟩
        · intro u
          simp [M3B.ECLayout.gateSlots]
          erw [finSumFinEquiv_symm_apply_castAdd]
          rfl
      | right s =>
        let i := FpArithNet.blockIndex s
        let j := FpChainBijection.coord s
        obtain ⟨h₁,h₂⟩ := seed_fields F seed P T y η i
        obtain ⟨hs,hi⟩ := lookup_fields F seed P T y η i
        apply fpEntry_lookup_vertex_v2 Q w A B t sl adr hm hp hl hc s i j rfl _ _ hs
          (fun x => (((seed i).1.val+1)*x+(seed i).2.val)%p) _ _ _
          (hash_injective seed F i (hF i)) a
        · simp [M3B.ECLayout.gateSlots,numbering,i,j,FpArithNet.whichSide]
          erw [finSumFinEquiv_symm_apply_natAdd]
          rfl
        · exact address_at A B s
        · intro x;rw [hpr,h₁,h₂]
        · intro r;rw [(hi r).1];rfl
        · intro r;exact (hi r).2

end DetDLP.M3A.Witness
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DetDLP.M3A.Witness
open FpPolyDefs FpWireCore w4_M5Network

theorem transport {q : w3_Query} {C : ℕ} (W : w3_WireCore q C) (desc : List Bool) (S : ℕ)
    (G : WireGraph) (t : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly (w3_precision q) (w3_len q))
    (hd : W.desc=desc) (hs : W.S=S) (hg : W.G=G) (ht : HEq W.T t)
    (bounds : G.subdivision.nV ≤ (S+desc.length+1)^5 ∧ ∀ v a,
      (encodePortQuery desc (v : Fin G.subdivision.nV).val (List.ofFn (a : Fin (G.subdivision.deg v) → Bool))).length+1 ≤ (S+desc.length+1)^5)
    (entries : ∀ v a, EncodesTruncPoly (w3_precision q) (w3_len q)
      (fpEntry (encodePortQuery desc (v : Fin G.subdivision.nV).val (List.ofFn a))) (w3_liftTensor G t v a)) :
    W.G.subdivision.nV ≤ (W.S+W.desc.length+1)^5 ∧ ∀ v a,
      let w := encodePortQuery W.desc (v : Fin W.G.subdivision.nV).val (List.ofFn a)
      w.length+1 ≤ (W.S+W.desc.length+1)^5 ∧
        EncodesTruncPoly (w3_precision q) (w3_len q) (fpEntry w) (w3_liftTensor W.G W.T v a) := by
  cases W with
  | mk wg wl ws wd wt check decode live dead cnt deg ori edg dege deq shp =>
    dsimp only at *
    subst wg; subst ws; subst wd
    obtain rfl := eq_of_heq ht
    exact ⟨bounds.1,fun v a => ⟨bounds.2 v a,entries v a⟩⟩

end DetDLP.M3A.Witness

open DetDLP DetDLP.M3A Groundwork
open DetDLP.M3A.Witness DetDLP.M3A.FpPolyDefs DetDLP.M3A.FpWireCore

private theorem nativeQueryWitness (mul : w3_modMulInterface)
    (hcore : FpWireCore.CoreFamily) :
    ∃ c : ℕ, 0 < c ∧
      ∀ q, w3_fpQueries q → ∃ W : w3_WireCore q 1000000,
        FpPolyDefs.fpBuild q.input = w3_wirePacket W ∧
        W.G.subdivision.nV ≤ (W.S + W.desc.length + 1) ^ c ∧
        ∀ (v : Fin W.G.subdivision.nV) (a : Fin (W.G.subdivision.deg v) → Bool),
          let w := encodePortQuery W.desc v.val (List.ofFn a)
          w.length + 1 ≤ (W.S + W.desc.length + 1) ^ c ∧
          EncodesTruncPoly (w3_precision q) (w3_len q) (FpPolyDefs.fpEntry w)
            (w3_liftTensor W.G W.T v a) := by
  refine ⟨5,by decide,?_⟩
  intro qq hqq
  have hqq' := hqq
  obtain ⟨p,prime,h67,hNZ,h64,h4096,seed,F,hF,P,y,η,rfl⟩ := hqq
  let D := bitLen p
  let M := p-1
  let m := blockCount D
  let T := hashThreshold p M m M
  let K := Nat.clog 2 (2*T)
  let nz : NeZero M := ⟨Nat.ne_of_gt hNZ⟩
  let w := Witness.input F seed P T y η
  let q := native F seed P η nz y w D K
  have hq : w3_fpQueries q := hqq'
  change ∃ W : w3_WireCore q 1000000, fpBuild q.input=w3_wirePacket W ∧ _
  have hf := w3_fpPrimeFits prime.out (by omega : 2<p)
  have hd : 2 ≤ D := by
    by_contra! h
    have he := Nat.pow_le_pow_right (by decide : 0<2) (show bitLen p ≤ 1 from (by change D ≤ 1;omega))
    norm_num at he;omega
  have hm : 1 ≤ m := (by decide : 1 ≤ 2).trans (le_max_left ..)
  have hfit : T ≤ 2^K := (by omega : T ≤ 2*T).trans (Nat.le_pow_clog (by decide) _)
  obtain ⟨W,hW⟩ := hcore.2 (d:=D) (k:=K) (T:=T) F seed P η nz y w hf.1
    hd rfl (by omega) hf.2 hfit hm hF mul hq
  have hW' := hW
  obtain ⟨hdesc,hS,hG,_,ht⟩ := hW
  obtain ⟨hwM,hwD,hwK,hη,_,_,_,hp,hl,_⟩ := input_meta F seed P T y η nz
  refine ⟨W,?_,?_⟩
  · exact Witness.packet_of_fields F seed P η nz y w hf.1 ⟨hwM,hwD,hwK,hη,hp,hl⟩ W hW'
  · exact Witness.transport W w (budget m D K (w3_precision q)) _ _ hdesc hS hG ht
      (Witness.input_bounds hf.1 m K η (w3_precision q) w)
      (native_entries F seed P T nz y η hf.1 (fun i => (hF i).1))


end

open DetDLP DetDLP.M3A

theorem solution : w3_polyWireFamily w3_fpQueries := by
  obtain ⟨c, hc, hwit⟩ := nativeQueryWitness w3_m5_modmul_r2 FpWireCore.native_core_family
  exact ⟨1000000, c, FpPolyDefs.fpBuild, FpPolyDefs.fpEntry, by omega, hc,
    FpPolyDefs.fpBuild_poly, FpPolyDefs.fpEntry_poly, hwit⟩
