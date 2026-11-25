-- Prove2me | solution 1 for DetDLP.M3A.FpPolyDefs.fpBuild_poly
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T21:46:17.0911+00:00
-- url     : https://prove2.me/submissions/011d475d-b978-48a0-a180-47c25034a99f

import Theorems.Thm_DetDLP_M3A_FpPolyDefs_numeric_uniform
import Theorems.Thm_Groundwork_Unary_of_le
import Theorems.Thm_Groundwork_Unary_of_length
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace DetDLP.M3A.FpPolyDefs
open Groundwork S8H.PointAddresses S8L.FpPair.Address w4_MulParams w4_M5GraphBounds
attribute [local fun_prop] PolyT.const PolyT.add PolyT.mul PolyT.sub PolyT.length PolyT.getD PolyT.id' PolyT.comp PolyT.bits PolyT.fst PolyT.snd PolyT.prodMk PolyT.map PolyT.append m89_enum_words.fields_poly w5_M6Sort.decode_poly w5_M6Sort.cw_poly DetDLP_W1_Queries.frame_poly P2M_Groundwork_PolyT_id__1c5d0f44cc8f
private theorem uadd {α} [Enc α] {f g : α → ℕ} (hf : Unary f) (hg : Unary g) : Unary (fun x => f x+g x) := by
  apply (PolyT.append hf hg).congr;intro x;rw [List.replicate_add]
private theorem umul {α} [Enc α] {f g : α → ℕ} (hf : Unary f) (hg : Unary g) : Unary (fun x => f x*g x) := by
  have H := PolyT.flatMap (f:=fun x (_ : Unit) => List.replicate (g x) ()) (PolyT.comp hg (PolyT.fst PolyT.id')) hf
  apply H.congr;intro x;change _ = List.replicate (f x*g x) ();generalize f x=n;induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ,List.flatMap_cons,ih,Nat.succ_mul];rw [← List.replicate_add,Nat.add_comm]
private theorem uconst {α} [Enc α] (k : ℕ) : Unary (fun _ : α => k) := PolyT.const _
private theorem sizes (M D K n : ℕ) : let c := whole M D K n; c.ng+c.nb+c.ne+c.ne ≤ 1000000*(M+1)*(D+K+n+1) := by
  intro c
  have H : (mul D).ng ≤ 256*(D+1) ∧ (mul D).nb ≤ 1100*(D+1) := by
    cases D with
    | zero => decide
    | succ D =>
      have hd : 1 ≤ D+1 := by omega
      have h1 := J_lt_linear hd; have h2 := n0_upper hd;have h3 := L_le_half_J hd;have h4 := L1_le_L (D+1);have h5 := L2_le_L (D+1)
      refine ⟨?_,by change wires (D+1) ≤ _;rw [wires_eq hd];exact (graph_edge_bound hd).le⟩
      change vertexCount (D+1) ≤ _;unfold vertexCount;rw [Nat.mul_comm (L2 _) (L1 _),L1_mul_L2];omega
  let u := (mul D).ng;let v := (mul D).nb
  have g : (slot D K).ng = (u+u+2*D+(2*D+2*D)+8*(D+1)+(3*D+5*(D+1))+K+min K (D+1)) := by rfl
  have b : (slot D K).nb = (2*v+2*D*4+8*(D+1)*4+K) := by dsimp [slot,FpSlotTile.slotCode];change v+v+2*D*4+8*(D+1)*4+K=_;ring
  have e : (slot D K).ne = 4*v+2*D*5+2*(2*D+2*D)+8*(D+1)*5+2*(3*D+5*(D+1))+K+2*min K (D+1) := by change v+v+(v+v)+2*D*5+((2*D+2*D)+(2*D+2*D))+8*(D+1)*5+((3*D+5*(D+1))+(3*D+5*(D+1)))+K+(min K (D+1)+min K (D+1))=_;ring
  have hu : u ≤ 256*(D+1) := H.1;have hv : v ≤ 1100*(D+1) := H.2
  have gu : (stage D).ng = u+u+2*D+4*D+(D+1)+D := rfl
  have bu : (stage D).nb = v+v+2*D*4+(D+1)*4 := rfl
  have eu : (stage D).ne = v+v+(v+v)+2*D*5+(4*D+4*D)+(D+1)*5+(D+D) := rfl
  simp only [c,whole,M3B.ECLayout.code,arith,chains,base,splice,sum,repeatCode,S8H0.AnchoredLayout.anchorCode,g,b,e,gu,bu,eu]
  nlinarith only [Nat.mul_le_mul_left M hu,Nat.mul_le_mul_left M hv,Nat.mul_le_mul_left M (min_le_left K (D+1)),min_le_left n (4*M*D)]
attribute [local fun_prop] PolyT.sub PolyT.mul PolyT.div PolyT.mod P2M_Groundwork_PolyT_cons__3a60f43a3b86
private theorem params : PolyT d ∧ PolyT m ∧ PolyT k ∧ PolyT pre ∧ PolyT sizeField ∧ PolyT prec ∧ PolyT len := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first | unfold d | unfold m | unfold k | unfold pre | unfold sizeField | unfold prec | unfold len
  all_goals dsimp only [d,m,k,pre,prec,len,width,num,field,nums,fld,prime,threshold,groupSize,dFilt];fun_prop
private abbrev graph (w : W) := whole (m w) (d w) (k w) (pre w).length
private theorem ranges : Unary (fun w => (graph w).ng+(graph w).nb+(graph w).ne) ∧ Unary (fun w => (graph w).ne+(graph w).ne) := by
  obtain ⟨hd,hm,hk,hp,_,_,_⟩ := params
  have uD : Unary d := by unfold d width; apply Unary.of_length;unfold prime num nums field fld;fun_prop
  have uK : Unary k := by unfold k width; apply Unary.of_length;unfold threshold num nums field fld;fun_prop
  have uM : Unary m := by unfold m;apply Unary.of_length;unfold fld field;fun_prop
  have uN := Unary.of_length hp
  have u := umul (umul (uconst 1000000) (uadd uM (uconst 1))) (uadd (uadd (uadd uD uK) uN) (uconst 1))
  obtain ⟨ng,nb,ne,_,_⟩ := numeric_uniform hm hd hk (PolyT.length hp) (PolyT.const 0)
  have B (w : W) := sizes (m w) (d w) (k w) (pre w).length
  constructor
  · exact Unary.of_le u (PolyT.add (PolyT.add ng nb) ne) (fun w => (Nat.le_add_right ..).trans (B w))
  · exact Unary.of_le u (PolyT.add ne ne) (fun w => by have h := B w;change _ ≤ 1000000*(m w+1)*(d w+k w+(pre w).length+1);dsimp only at h;change (graph w).ne+(graph w).ne ≤ _;change (graph w).ng+(graph w).nb+(graph w).ne+(graph w).ne ≤ _ at h;omega)

private theorem pushFrame {a b : W → W} (ha : PolyT a) (hb : PolyT b) : PolyT (fun w => true :: (OAI.Algorithms.SubexponentialSAT.Encoding.frame (a w) ++ b w)) := by
  simp only [← DetDLP_W1_Queries.frame_correct]; exact P2M_Groundwork_PolyT_cons__3a60f43a3b86 (PolyT.const true) (PolyT.append (DetDLP_W1_Queries.frame_poly ha) hb)

theorem fpBuild_poly : PolyT fpBuild := by
  obtain ⟨hd,hm,hk,hp,hs,hprec,hlen⟩ := params
  obtain ⟨ng,nb,ne,_,_⟩ := numeric_uniform hm hd hk (PolyT.length hp) (PolyT.const 0)
  have fst := PolyT.fst (PolyT.id' (α:=W × ℕ));have snd := PolyT.snd (PolyT.id' (α:=W × ℕ))
  obtain ⟨_,_,_,src,dst⟩ := numeric_uniform (PolyT.comp hm fst) (PolyT.comp hd fst) (PolyT.comp hk fst) (PolyT.comp (PolyT.length hp) fst) snd
  have upper := PolyT.comp ng fst
  have gr : PolyT (fun w : W => S8H.WirePacket.packet ((graph w).ng+(graph w).nb) (graph w).ne (graph w).gate (fun j => (graph w).ng+(graph w).bit j)) := S8H.WirePacket.packet_poly (PolyT.add ng nb) ne ranges.1 ranges.2 src (PolyT.add upper dst)
  have mask : PolyT (fun w : W => (List.range ((graph w).ng+(graph w).nb+(graph w).ne)).map (fun v => decide ((arith (m w) (d w) (k w) (pre w).length).ng ≤ v ∧ v < (graph w).ng))) := by
    have lower : PolyT (fun x : W × ℕ => (arith (m x.1) (d x.1) (k x.1) (pre x.1).length).ng) := by
      apply (PolyT.sub (PolyT.comp ng fst) (PolyT.mul (PolyT.const 4) (PolyT.comp hm fst))).congr; intro x; change (_+4*m x.1)-4*m x.1=_;omega
    exact PolyT.map (f:=fun w v => decide ((arith (m w) (d w) (k w) (pre w).length).ng ≤ v ∧ v < (graph w).ng)) (PolyT.decide_and (PolyT.decide_le lower snd) (PolyT.decide_lt snd upper)) (PolyT.range ranges.1)
  have last := pushFrame mask (PolyT.const [false])
  have l := pushFrame (w5_M6Sort.cw_poly hlen) last
  have p := pushFrame (w5_M6Sort.cw_poly hprec) l
  have s := pushFrame (w5_M6Sort.cw_poly hs) p
  have K := pushFrame (w5_M6Sort.cw_poly hk) s
  have M := pushFrame (w5_M6Sort.cw_poly hm) K
  have D := pushFrame (w5_M6Sort.cw_poly hd) M
  have result := pushFrame (PolyT.id' (α:=W)) (pushFrame gr D)
  unfold fpBuild; dsimp only [OAI.Algorithms.SubexponentialSAT.Encoding.encodeList,id_eq];exact result

end DetDLP.M3A.FpPolyDefs

theorem solution : Groundwork.PolyT DetDLP.M3A.FpPolyDefs.fpBuild := DetDLP.M3A.FpPolyDefs.fpBuild_poly
