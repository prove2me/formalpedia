-- Prove2me | solution 1 for FasterDistributedMatching.ApproximateMatching.fmu_local_booster
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:48:44.255475+00:00
-- url     : https://prove2.me/submissions/743fdcaa-1b24-4866-82e9-8319cb59a062

import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Routing
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Basic
import Theorems.Thm_Timetabling85_ClassTeacher_prop_2_1
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_StageData
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Virtual
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Local
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
set_option linter.all false
set_option maxRecDepth 4096
open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace wA
variable {N: ℕ} (G: SimpleGraph (Fin N))
lemma BH (e: Sym2 (Fin N)):∃v,v∈ e:= by
 obtain ⟨⟨u,v⟩,rfl⟩:= e.exists_rep
 exact ⟨u,Sym2.mem_mk_left _ _⟩
lemma Al:∃M: Finset G.edgeSet,SemiStreamMWM.IsMatching G M∧ M.card= optimum G:= by
 have hempty:(∅: Finset G.edgeSet)∈ SemiStreamMWM.matchings G:= by
   simp [SemiStreamMWM.matchings,SemiStreamMWM.IsMatching]
 obtain ⟨M,hM,hcard⟩:= exists_mem_eq_sup (SemiStreamMWM.matchings G) ⟨∅,hempty⟩ Finset.card
 exact ⟨M,(mem_filter.mp hM).2,hcard.symm⟩
lemma Eh (M: Finset G.edgeSet) (hM: SemiStreamMWM.IsMatching G M) (hcard: M.card= optimum G)
   (e: G.edgeSet):∃f∈ M,∃v,v∈ e.val∧ v∈ f.val:= by
 by_contra hcover
 have hdisj:∀f∈ M,∀v∈ e.val,v∉ f.val:= by
   intro f hf v hve hvf
   exact hcover ⟨f,hf,v,hve,hvf⟩
 have heM: e∉ M:= by
   intro he
   obtain ⟨v,hv⟩:= BH e.val
   exact hdisj e he v hv hv
 have hins: SemiStreamMWM.IsMatching G (insert e M):= by
   intro a ha b hb hab v hva
   rcases mem_insert.mp ha with hae|haM
   · subst a
     rcases mem_insert.mp hb with hbe|hbM
     · exact (hab hbe.symm).elim
     · exact hdisj b hbM v hva
   · rcases mem_insert.mp hb with hbe|hbM
     · subst b
       intro hve
       exact hdisj a haM v hve hva
     · exact hM a haM b hbM hab v hva
 have hle:(insert e M).card≤ optimum G:= by
   exact le_sup (f:=Finset.card) (mem_filter.mpr ⟨mem_univ _,hins⟩)
 rw [card_insert_of_notMem heM,hcard] at hle
 omega
end wA
end
noncomputable section
namespace zD
section Restrict
variable {V: Type} [Fintype V] [DecidableEq V] (H: SimpleGraph V) (S: Finset (Sym2 V))
def GB: SimpleGraph V where
 Adj a b:= H.Adj a b∧ s(a,b)∈ S
 symm:=⟨by rintro a b ⟨h,he⟩; exact ⟨h.symm,by simpa only [Sym2.eq_swap] using he⟩⟩
 loopless:=⟨by intro a h; exact h.1.ne rfl⟩
lemma AN: GB H S≤ H:= fun _ _ h=> h.1
lemma g4 (hS: S ⊆H.edgeFinset):(GB H S).edgeFinset= S:= by
 ext e
 obtain ⟨⟨u,v⟩,rfl⟩:= e.exists_rep
 change s(u,v)∈(GB H S).edgeFinset↔ s(u,v)∈ S
 rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
 change (H.Adj u v∧ s(u,v)∈ S)↔ s(u,v)∈ S
 exact ⟨And.right,fun h=>⟨H.mem_edgeSet.mp (H.mem_edgeFinset.mp (hS h)),h⟩⟩
end Restrict
end zD
end
noncomputable section
namespace wA
variable {N: ℕ} (G: SimpleGraph (Fin N))
def LC (M: Finset G.edgeSet): SimpleGraph (Fin N):=
 zD.GB G (M.image Subtype.val)
lemma oX (M: Finset G.edgeSet):(LC G M).edgeFinset= M.image Subtype.val:= by
 apply zD.g4
 intro e he
 obtain ⟨f,hf,rfl⟩:= mem_image.mp he
 exact G.mem_edgeFinset.mpr f.property
lemma tX (M: Finset G.edgeSet) (hM: SemiStreamMWM.IsMatching G M): Matching G (LC G M):= by
 refine ⟨zD.AN _ _,?_⟩
 intro e he f hf hne v hve hvf
 have heG: e.val∈ M.image Subtype.val:= by
   rw [←oX G M]
   exact (LC G M).mem_edgeFinset.mpr e.property
 have hfG: f.val∈ M.image Subtype.val:= by
   rw [←oX G M]
   exact (LC G M).mem_edgeFinset.mpr f.property
 obtain ⟨a,ha,hae⟩:= mem_image.mp heG
 obtain ⟨b,hb,hbf⟩:= mem_image.mp hfG
 have hab: a≠ b:= fun hh=> hne (Subtype.ext (hae.symm.trans (hh ▸hbf)))
 exact hM a ha b hb hab v (hae ▸hve) (hbf ▸hvf)
lemma DB (M: Finset G.edgeSet): matchingSize (LC G M)= M.card:= by
 unfold matchingSize
 rw [oX,card_image_of_injective _ Subtype.val_injective]
end wA
end
noncomputable section
namespace G5
variable {V W: Type} [DecidableEq V] [DecidableEq W]
def pairs: List V→ List (Finset V)
 | [] => []
 | [a] => [{a}]
 | a::b::rest => {a,b}::pairs rest
end G5
end
noncomputable section
namespace G5
section Sorted
variable {V: Type} [DecidableEq V] (S: Finset V) (key: V→ ℕ) (hi: Function.Injective key)
def MX: List V:= by
 letI:= LinearOrder.lift' key hi
 exact S.sort
lemma HU (v: V): v∈ MX S key hi↔ v∈ S:= by
 unfold MX
 exact Finset.mem_sort _
end Sorted
variable {N: ℕ} (G: SimpleGraph (Fin N)) (x: Sym2 (Fin N)→ ℝ) (q: ℝ)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids)
end G5
end
noncomputable section
namespace tB
section Selection
variable {V: Type} [DecidableEq V] (ids: V→ ℕ) (hi: Function.Injective ids)
def least (S: Finset V): Option V:=(G5.MX S ids hi).head?
lemma LQ (S: Finset V) (v: V) (hv: least ids hi S= some v): v∈ S:= by
 apply (G5.HU S ids hi v).mp
 have hmem: v∈ least ids hi S:= by rw [hv]; exact Option.mem_def.mpr rfl
 exact List.mem_of_mem_head? hmem
lemma D7 (S: Finset V) (hS: S.Nonempty):∃v,least ids hi S= some v:= by
 cases h: least ids hi S with
 | none =>
   have he: G5.MX S ids hi=[]:= List.head?_eq_none_iff.mp h
   obtain ⟨v,hv⟩:= hS
   have hv':=(G5.HU S ids hi v).mpr hv
   rw [he] at hv'
   exact (List.not_mem_nil hv').elim
 | some v => exact ⟨v,rfl⟩
end Selection
section Proposals
variable {V: Type} [Fintype V] [DecidableEq V] (H: SimpleGraph V)
   (side: V→ Bool) (hside:∀u v,H.Adj u v→ side u≠ side v)
   (ids: V→ ℕ) (hi: Function.Injective ids)
def Free (M: SimpleGraph V) (v: V): Prop:=∀w,¬M.Adj v w
end Proposals
end tB
end
noncomputable section
namespace tB
variable {V: Type} [Fintype V] [DecidableEq V]
   (ids: V→ ℕ) (hi: Function.Injective ids) (M: SimpleGraph V)
def NW (v: V): Option V:= least ids hi (M.neighborFinset v)
lemma LW (hM:∀u v w,M.Adj u v→ M.Adj u w→ v= w) (u v: V):
   NW ids hi M u= some v↔ M.Adj u v:= by
 constructor
 · intro h
   exact (SimpleGraph.mem_neighborFinset M u v).mp (LQ ids hi _ v h)
 · intro h
   obtain ⟨w,hw⟩:= D7 ids hi (M.neighborFinset u)
     ⟨v,(SimpleGraph.mem_neighborFinset M u v).mpr h⟩
   have huw:=(SimpleGraph.mem_neighborFinset M u w).mp (LQ ids hi _ w hw)
   have heq:= hM u w v huw h
   exact hw.trans (congrArg some heq)
lemma LV (u: V): NW ids hi M u= none↔ Free M u:= by
 constructor
 · intro h w hw
   obtain ⟨v,hv⟩:= D7 ids hi (M.neighborFinset u)
     ⟨w,(SimpleGraph.mem_neighborFinset M u w).mpr hw⟩
   change NW ids hi M u= some v at hv
   rw [h] at hv
   cases hv
 · intro h
   cases hm: NW ids hi M u with
   | none => rfl
   | some v =>
     have hv:=(SimpleGraph.mem_neighborFinset M u v).mp (LQ ids hi _ v hm)
     exact (h v hv).elim
lemma n4 {N: ℕ} (G M: SimpleGraph (Fin N)) (hsub: M≤ G)
   (hM:∀u v w,M.Adj u v→ M.Adj u w→ v= w): Matching G M:= by
 refine ⟨hsub,?_⟩
 intro e he f hf hne v hve hvf
 obtain ⟨u,hu⟩:= Sym2.mem_iff_exists.mp hve
 obtain ⟨w,hw⟩:= Sym2.mem_iff_exists.mp hvf
 have hvu: M.Adj v u:= M.mem_edgeSet.mp (by rw [←hu]; exact e.property)
 have hvw: M.Adj v w:= M.mem_edgeSet.mp (by rw [←hw]; exact f.property)
 have heq:= hM v u w hvu hvw
 exact hne (Subtype.ext (hu.trans ((congrArg (fun z=> s(v,z)) heq).trans hw.symm)))
lemma uZ {N: ℕ} (G M: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (hi: Function.Injective ids) (hsub: M≤ G)
   (hM:∀u v w,M.Adj u v→ M.Adj u w→ v= w):
   ReportsMatching G ids (fun v=>(NW ids hi M v).map ids) M:= by
 refine ⟨n4 G M hsub hM,?_⟩
 intro v
 constructor
 · rw [Option.map_eq_none_iff,LV]
   rfl
 · intro j
   constructor
   · intro h
     obtain ⟨w,hw,hj⟩:= Option.map_eq_some_iff.mp h
     exact ⟨w,(LW ids hi M hM v w).mp hw,hj⟩
   · rintro ⟨w,hw,hj⟩
     dsimp only
     rw [(LW ids hi M hM v w).mpr hw]
     exact congrArg some hj
end tB
end
noncomputable section
namespace qJ
variable {N: ℕ}
abbrev Nu (N: ℕ):= Fin N ⊕Fin N
def side: Nu N→ Bool
 | .inl _ => false
 | .inr _ => true
lemma gP (G M: SimpleGraph (Fin N)) (hM: Matching G M):
   ∀u v w,M.Adj u v→ M.Adj u w→ v= w:= by
 intro u v w huv huw
 by_contra hne
 let e: M.edgeSet:=⟨s(u,v),M.mem_edgeSet.mpr huv⟩
 let f: M.edgeSet:=⟨s(u,w),M.mem_edgeSet.mpr huw⟩
 have hef: e≠ f:= by
   intro he
   exact hne (Sym2.congr_right.mp (congrArg Subtype.val he))
 exact hM.2 e (mem_univ _) f (mem_univ _) hef u (Sym2.mem_mk_left _ _) (Sym2.mem_mk_left _ _)
end qJ
end
noncomputable section
namespace Be
variable {N: ℕ}
def exchange (M R S: SimpleGraph (Fin N)): SimpleGraph (Fin N):=(M \R) ⊔S
lemma wY (G M R S: SimpleGraph (Fin N)) (hM: Matching G M)
   (hS: Matching G S)
   (hremove:∀u v w,S.Adj u v→ M.Adj u w→ R.Adj u w):
   Matching G (exchange M R S):= by
 apply tB.n4 G _
 · intro u v h
   rcases h with h| h
   · exact hM.1 h.1
   · exact hS.1 h
 · intro u v w huv huw
   rcases huv with huv| huv<;> rcases huw with huw| huw
   · exact qJ.gP G M hM u v w huv.1 huw.1
   · exact (huv.2 (hremove u w v huw huv.1)).elim
   · exact (huw.2 (hremove u v w huv huw.1)).elim
   · exact qJ.gP G S hS u v w huv huw
lemma DK (M R S: SimpleGraph (Fin N)):
   (exchange M R S).edgeFinset=(M.edgeFinset \R.edgeFinset) ∪S.edgeFinset:= by
 ext e
 rw [mem_union,mem_sdiff,(exchange M R S).mem_edgeFinset,M.mem_edgeFinset,R.mem_edgeFinset,S.mem_edgeFinset]
 change e∈(M \R ⊔S).edgeSet↔ _
 rw [SimpleGraph.edgeSet_sup,SimpleGraph.edgeSet_sdiff]
 rfl
lemma FM (M R S: SimpleGraph (Fin N)) (hR: R≤ M) (hdis: Disjoint M.edgeFinset S.edgeFinset):
   matchingSize (exchange M R S)+matchingSize R= matchingSize M+matchingSize S:= by
 have hd: Disjoint (M.edgeFinset \R.edgeFinset) S.edgeFinset:= hdis.mono_left sdiff_subset
 have hc:= card_sdiff_add_card_eq_card (SimpleGraph.edgeFinset_mono hR)
 unfold matchingSize
 rw [DK,card_union_of_disjoint hd]
 omega
lemma FL (M R S: SimpleGraph (Fin N)) (hR: R≤ M) (hdis: Disjoint M.edgeFinset S.edgeFinset)
   (g: ℕ) (hgain: matchingSize S= matchingSize R+g):
   matchingSize (exchange M R S)= matchingSize M+g:= by
 have h:= FM M R S hR hdis
 omega
end Be
end
noncomputable section
namespace Be
variable {N: ℕ}
structure C3 (G M: SimpleGraph (Fin N)) where
 length: ℕ
 vertex: ℕ→ Fin N
 injective:∀i j,i≤ 2*length+1→ j≤ 2*length+1→ vertex i= vertex j→ i= j
 Mu:∀i,i≤ 2*length→ G.Adj (vertex i) (vertex (i+1))
 MG:∀i,i≤ 2*length→(M.Adj (vertex i) (vertex (i+1))↔ Odd i)
 Ki:∀w,¬M.Adj (vertex 0) w
 LP:∀w,¬M.Adj (vertex (2*length+1)) w
namespace C3
variable {G M: SimpleGraph (Fin N)} (P: C3 G M)
def J6: Finset (Sym2 (Fin N)):=(range (P.length+1)).image (fun i=> s(P.vertex (2*i),P.vertex (2*i+1)))
def Il: Finset (Sym2 (Fin N)):=(range P.length).image (fun i=> s(P.vertex (2*i+1),P.vertex (2*i+2)))
def added: SimpleGraph (Fin N):= zD.GB G P.J6
def Nm: SimpleGraph (Fin N):= zD.GB G P.Il
def support: Finset (Fin N):=(range (2*P.length+2)).image P.vertex
lemma Ha: P.J6 ⊆G.edgeFinset:= by
 intro e he
 obtain ⟨i,hi,rfl⟩:= mem_image.mp he
 exact G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr (P.Mu (2*i) (by have h:=mem_range.mp hi;omega)))
lemma EM: P.Il ⊆G.edgeFinset:= by
 intro e he
 obtain ⟨i,hi,rfl⟩:= mem_image.mp he
 have h:= P.Mu (2*i+1) (by have h:=mem_range.mp hi;omega)
 convert G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr h) using 1<;> congr 2<;> omega
lemma IT: P.added.edgeFinset= P.J6:=
 zD.g4 G _ P.Ha
lemma Gx: P.Nm.edgeFinset= P.Il:=
 zD.g4 G _ P.EM
lemma DC (a b: ℕ) (ha: a≤ 2*P.length) (hb: b≤ 2*P.length)
   (h: s(P.vertex a,P.vertex (a+1))= s(P.vertex b,P.vertex (b+1))): a= b:= by
 rcases Sym2.eq_iff.mp h with h| h
 · exact P.injective a b (by omega) (by omega) h.1
 · have h1:= P.injective a (b+1) (by omega) (by omega) h.1
   have h2:= P.injective (a+1) b (by omega) (by omega) h.2
   omega
lemma J7: matchingSize P.added= P.length+1:= by
 unfold matchingSize
 rw [P.IT,J6,card_image_of_injOn]
 · exact card_range _
 · intro i hi j hj heq
   have h:= P.DC (2*i) (2*j) (by have h:=mem_range.mp hi;omega) (by have h:=mem_range.mp hj;omega) heq
   omega
lemma Io: matchingSize P.Nm= P.length:= by
 unfold matchingSize
 rw [P.Gx,Il,card_image_of_injOn]
 · exact card_range _
 · intro i hi j hj heq
   have heq': s(P.vertex (2*i+1),P.vertex ((2*i+1)+1))= s(P.vertex (2*j+1),P.vertex ((2*j+1)+1)):= by
     convert heq using 1<;> congr 2<;> omega
   have h:= P.DC (2*i+1) (2*j+1) (by have h:=mem_range.mp hi;omega) (by have h:=mem_range.mp hj;omega) heq'
   omega
end C3
end Be
end
noncomputable section
namespace Be
variable {N: ℕ}
structure v9 (G M: SimpleGraph (Fin N)) (root: Fin N) where
 length: ℕ
 vertex: ℕ→ Fin N
 first: vertex 0= root
 injective:∀i j,i≤ 2*length→ j≤ 2*length→ vertex i= vertex j→ i= j
 Mu:∀i,i< 2*length→ G.Adj (vertex i) (vertex (i+1))
 MG:∀i,i< 2*length→(M.Adj (vertex i) (vertex (i+1))↔ Odd i)
 L9:∀w,¬M.Adj root w
namespace v9
variable {G M: SimpleGraph (Fin N)} {root: Fin N} (P: v9 G M root)
def trivial (G M: SimpleGraph (Fin N)) (root: Fin N) (hroot:∀w,¬M.Adj root w): v9 G M root where
 length:= 0
 vertex:= fun _=> root
 first:= rfl
 injective:= by intros;omega
 Mu:= by intros;omega
 MG:= by intros;omega
 L9:= hroot
def support: Finset (Fin N):=(range (2*P.length+1)).image P.vertex
def Nv (NS: Finset (Fin N ×Fin N)): Prop:=
 ∀i,i< 2*P.length→(P.vertex i,P.vertex (i+1))∈ NS
def Mq (ell: ℕ) (labels: Fin N ×Fin N→ ℕ): Prop:=
 P.length≤ ell∧∀i,i< P.length→ labels (P.vertex (2*i+1),P.vertex (2*i+2))≤ i+1
def M4 (Q: v9 G M root): Prop:=
 P.length≤ Q.length∧∀i,i≤ 2*P.length→ Q.vertex i= P.vertex i
lemma mem_support (i: ℕ) (hi: i≤ 2*P.length): P.vertex i∈ P.support:=
 mem_image.mpr ⟨i,mem_range.mpr (by omega),rfl⟩
lemma MU: root∈ P.support:= by simpa only [P.first] using P.mem_support 0 (by omega)
lemma IB: P.support.card= 2*P.length+1:= by
 unfold support
 rw [card_image_of_injOn]
 · exact card_range _
 · intro i hi j hj heq
   exact P.injective i j (by have h:=mem_range.mp hi;omega) (by have h:=mem_range.mp hj;omega) heq
lemma HR (i: ℕ) (hi: i< P.length):
   M.Adj (P.vertex (2*i+1)) (P.vertex (2*i+2)):= by
 have hh:=(P.MG (2*i+1) (by omega)).mpr ⟨i,by omega⟩
 convert hh using 1
lemma Hs: P.M4 P:=⟨le_rfl,fun _ _=> rfl⟩
lemma FP {Q R: v9 G M root} (hPQ: P.M4 Q) (hQR: Q.M4 R): P.M4 R:= by
 refine ⟨hPQ.1.trans hQR.1,?_⟩
 intro i hi
 have hlength:= hPQ.1
 exact (hQR.2 i (by omega)).trans (hPQ.2 i hi)
end v9
end Be
end
noncomputable section
namespace Be
variable {N: ℕ}
def Mv (G: SimpleGraph (Fin N)) (NS: Finset (Fin N ×Fin N)): SimpleGraph (Fin N) where
 Adj u v:= G.Adj u v∧((u,v)∈ NS∨(v,u)∈ NS)
 symm:=⟨by rintro u v ⟨h,he⟩;exact ⟨h.symm,he.symm⟩⟩
 loopless:=⟨by intro v h;exact h.1.ne rfl⟩
namespace v9
variable {G M: SimpleGraph (Fin N)} {root: Fin N} (P: v9 G M root)
def Kt (NS: Finset (Fin N ×Fin N)) (hP: P.Nv NS): v9 (Mv G NS) M root where
 length:= P.length
 vertex:= P.vertex
 first:= P.first
 injective:= P.injective
 Mu:= fun i hi=>⟨P.Mu i hi,Or.inl (hP i hi)⟩
 MG:= P.MG
 L9:= P.L9
end v9
def C8 (M: SimpleGraph (Fin N)) (NS: Finset (Fin N ×Fin N)) (v: Fin N): Prop:=
 ∃u w,(u,w)∈ NS∧ M.Adj u w∧(v= u∨ v= w)
structure Bi (G M: SimpleGraph (Fin N)) (root: Fin N) where
 NS: Finset (Fin N ×Fin N)
 L9:∀w,¬M.Adj root w
 valid:∀u v,(u,v)∈ NS→ G.Adj u v
 xK:∀u v,(u,v)∈ NS→ M.Adj u v→
   ∃P: v9 G M root,0< P.length∧ P.Nv NS∧
     P.vertex (2*P.length-1)= u∧ P.vertex (2*P.length)= v
 LD:∀u v,(u,v)∈ NS→
   (u= root∨ C8 M NS u)∧(v= root∨ C8 M NS v)
namespace Bi
variable {G M: SimpleGraph (Fin N)} {root: Fin N} (S: Bi G M root)
def vertices: Finset (Fin N):={root} ∪S.NS.biUnion (fun e=>{e.1,e.2})
def HP: Finset (Sym2 (Fin N)):=(S.NS.filter (fun e=> M.Adj e.1 e.2)).image (fun e=> s(e.1,e.2))
def initial (G M: SimpleGraph (Fin N)) (root: Fin N) (hf:∀w,¬M.Adj root w): Bi G M root where
 NS:=∅
 L9:= hf
 valid:= by intros;simp_all
 xK:= by intros;simp_all
 LD:= by intros;simp_all
lemma MU: root∈ S.vertices:= mem_union_left _ (mem_singleton_self _)
lemma Ft (u v: Fin N) (h:(u,v)∈ S.NS): u∈ S.vertices∧ v∈ S.vertices:= by
 constructor
 · exact mem_union_right _ (mem_biUnion.mpr ⟨(u,v),h,mem_insert_self _ _⟩)
 · exact mem_union_right _ (mem_biUnion.mpr ⟨(u,v),h,mem_insert_of_mem (mem_singleton_self _)⟩)
lemma EA (P: v9 G M root) (hP: P.Nv S.NS): P.support ⊆S.vertices:= by
 intro v hv
 obtain ⟨i,hi,rfl⟩:= mem_image.mp hv
 have hi': i≤ 2*P.length:= by have h:=mem_range.mp hi;omega
 by_cases hi0: i= 0
 · subst i
   rw [P.first]
   exact S.MU
 · have he:= hP (i-1) (by omega)
   have hv:=(S.Ft (P.vertex (i-1)) (P.vertex ((i-1)+1)) he).2
   simpa only [Nat.sub_add_cancel (by omega: 1≤ i)] using hv
lemma wS (v: Fin N) (hv: v∈ S.vertices): v= root∨ C8 M S.NS v:= by
 rcases mem_union.mp hv with h|h
 · exact Or.inl (mem_singleton.mp h)
 · obtain ⟨⟨u,w⟩,huw,hv⟩:= mem_biUnion.mp h
   rcases mem_insert.mp hv with h|h
   · exact h ▸(S.LD u w huw).1
   · exact (mem_singleton.mp h) ▸(S.LD u w huw).2
lemma Hm (v: Fin N) (hv: C8 M S.NS v):∃w,M.Adj v w∧ w∈ S.vertices:= by
 obtain ⟨u,w,he,hm,hv⟩:= hv
 rcases hv with hv|hv
 · rw [hv]
   exact ⟨w,hm,(S.Ft u w he).2⟩
 · rw [hv]
   exact ⟨u,hm.symm,(S.Ft u w he).1⟩
lemma E5: S.vertices.card≤ 1+2*S.HP.card:= by
 have hsub: S.vertices ⊆{root} ∪S.HP.biUnion Sym2.toFinset:= by
   intro v hv
   rcases S.wS v hv with h|h
   · exact mem_union.mpr (Or.inl (mem_singleton.mpr h))
   · obtain ⟨u,w,he,hm,hv⟩:= h
     have heM: s(u,w)∈ S.HP:= mem_image.mpr ⟨(u,w),mem_filter.mpr ⟨he,hm⟩,rfl⟩
     exact mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨s(u,w),heM,Sym2.mem_toFinset.mpr (Sym2.mem_iff.mpr hv)⟩))
 have hends:(S.HP.biUnion Sym2.toFinset).card≤ 2*S.HP.card:= by
   calc
     _≤∑e∈ S.HP,e.toFinset.card:= card_biUnion_le
     _≤∑_∈ S.HP,(2:ℕ):= sum_le_sum (fun e _=> by rw [Sym2.card_toFinset];split_ifs<;>omega)
     _= _:= by simp [mul_comm]
 have hu:= card_union_le ({root}:Finset (Fin N)) (S.HP.biUnion Sym2.toFinset)
 simp only [card_singleton] at hu
 exact (card_le_card hsub).trans (by omega)
lemma rV: S.HP ⊆M.edgeFinset:= by
 intro e he
 change e∈(S.NS.filter (fun p=> M.Adj p.1 p.2)).image (fun p=> s(p.1,p.2)) at he
 obtain ⟨p,hp,hpe⟩:= mem_image.mp he
 rw [←hpe]
 exact M.mem_edgeFinset.mpr (M.mem_edgeSet.mpr (mem_filter.mp hp).2)
end Bi
end Be
end
noncomputable section
namespace Be.v9
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {root: Fin N} (P: v9 G M root)
def KA (i: ℕ): Fin N ×Fin N:=(P.vertex (2*i+1),P.vertex (2*i+2))
def Nl (labels: Fin N ×Fin N→ ℕ) (a: Fin N ×Fin N): ℕ:=
 if h:∃i,i< P.length∧ P.KA i= a then min (labels a) (h.choose+1) else labels a
lemma pB (i j: ℕ) (hi: i< P.length) (hj: j< P.length)
   (h: P.KA i= P.KA j): i= j:= by
 have hv:= congrArg Prod.fst h
 have hn:= P.injective (2*i+1) (2*j+1) (by omega) (by omega) hv
 omega
lemma KX (labels: Fin N ×Fin N→ ℕ) (i: ℕ) (hi: i< P.length):
   P.Nl labels (P.KA i)= min (labels (P.KA i)) (i+1):= by
 unfold Nl
 have hex:∃j,j< P.length∧ P.KA j= P.KA i:=⟨i,hi,rfl⟩
 rw [dif_pos hex]
 have hidx: hex.choose= i:= P.pB _ i hex.choose_spec.1 hi hex.choose_spec.2
 rw [hidx]
lemma Ik (labels: Fin N ×Fin N→ ℕ):∀a,P.Nl labels a≤ labels a:= by
 intro a
 unfold Nl
 split_ifs
 · exact min_le_left _ _
 · rfl
lemma AM (labels: Fin N ×Fin N→ ℕ) (hpos:∀a,1≤ labels a):∀a,1≤ P.Nl labels a:= by
 intro a
 unfold Nl
 split_ifs
 · exact le_min (hpos a) (by omega)
 · exact hpos a
lemma AL (labels: Fin N ×Fin N→ ℕ) (ell: ℕ) (hell: P.length≤ ell): P.Mq ell (P.Nl labels):= by
 refine ⟨hell,?_⟩
 intro i hi
 change P.Nl labels (P.KA i)≤ i+1
 rw [P.KX labels i hi]
 exact min_le_right _ _
lemma EI (labels: Fin N ×Fin N→ ℕ) (i: ℕ) (hi: i< P.length)
   (hlabel: i+1< labels (P.KA i)): P.Nl labels (P.KA i)< labels (P.KA i):= by
 rw [P.KX labels i hi,min_eq_right hlabel.le]
 exact hlabel
end Be.v9
end
noncomputable section
namespace Be
variable {N P: ℕ}
structure wF (G M: SimpleGraph (Fin N)) (H K: SimpleGraph (Fin P)) where
 toFun: Fin N→ Fin P
 injective: Function.Injective toFun
 LH:∀u v,H.Adj (toFun u) (toFun v)↔ G.Adj u v
 HS:∀u v,K.Adj (toFun u) (toFun v)↔ M.Adj u v
 B7:∀u w,K.Adj (toFun u) w→∃v,toFun v=w
namespace wF
variable {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)} (E: wF G M H K)
lemma free_map (u: Fin N) (hFree:∀v,¬M.Adj u v):∀w,¬K.Adj (E.toFun u) w:= by
 intro w hEdge
 obtain ⟨v,rfl⟩:=E.B7 u w hEdge
 exact hFree v ((E.HS u v).mp hEdge)
def pairMap (a: Fin N ×Fin N): Fin P ×Fin P:=(E.toFun a.1,E.toFun a.2)
def Nc (A: Finset (Fin N ×Fin N)): Finset (Fin P ×Fin P):=A.image E.pairMap
lemma x4: Function.Injective E.pairMap:= by
 rintro ⟨a,b⟩ ⟨c,d⟩ h
 obtain ⟨hAC,hBD⟩:=Prod.mk.inj h
 exact Prod.ext (E.injective hAC) (E.injective hBD)
lemma Jn (A: Finset (Fin N ×Fin N)) (u v: Fin N):
   (E.toFun u,E.toFun v)∈E.Nc A↔(u,v)∈A:= by
 constructor
 · intro h
   obtain ⟨a,ha,hEq⟩:=mem_image.mp h
   have hA: a=(u,v):=E.x4 hEq
   exact hA ▸ha
 · intro h;exact mem_image.mpr ⟨(u,v),h,rfl⟩
lemma Hg (A: Finset (Fin N ×Fin N)) (u v: Fin N):
   (Mv H (E.Nc A)).Adj (E.toFun u) (E.toFun v)↔(Mv G A).Adj u v:= by
 change (H.Adj (E.toFun u) (E.toFun v)∧
   ((E.toFun u,E.toFun v)∈E.Nc A∨(E.toFun v,E.toFun u)∈E.Nc A))↔ _
 rw [E.LH,E.Jn,E.Jn]
 rfl
def NH (A: Finset (Fin N ×Fin N)):
   wF (Mv G A) M (Mv H (E.Nc A)) K where
 toFun:=E.toFun
 injective:=E.injective
 LH:=E.Hg A
 HS:=E.HS
 B7:=E.B7
end wF
namespace v9
variable {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)} (E: wF G M H K)
   {r: Fin N} (Q: v9 G M r)
def Nd: v9 H K (E.toFun r) where
 length:=Q.length
 vertex:=fun i=>E.toFun (Q.vertex i)
 first:=congrArg E.toFun Q.first
 injective:=fun i j hi hj hEq=>Q.injective i j hi hj (E.injective hEq)
 Mu:=fun i hi=>(E.LH _ _).mpr (Q.Mu i hi)
 MG:=fun i hi=>(E.HS _ _).trans (Q.MG i hi)
 L9:=E.free_map r Q.L9
lemma B4:(Q.Nd E).support=Q.support.image E.toFun:= by
 unfold support
 rw [image_image]
 rfl
lemma Ed (A: Finset (Fin N ×Fin N)) (hInside: Q.Nv A):
   (Q.Nd E).Nv (E.Nc A):= by
 intro i hi
 exact mem_image.mpr ⟨(Q.vertex i,Q.vertex (i+1)),hInside i hi,rfl⟩
lemma uK (i: ℕ):(Q.Nd E).KA i=E.pairMap (Q.KA i):= rfl
end v9
namespace C3
variable {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)} (E: wF G M H K)
   (Q: C3 G M)
def Nd: C3 H K where
 length:=Q.length
 vertex:=fun i=>E.toFun (Q.vertex i)
 injective:=fun i j hi hj hEq=>Q.injective i j hi hj (E.injective hEq)
 Mu:=fun i hi=>(E.LH _ _).mpr (Q.Mu i hi)
 MG:=fun i hi=>(E.HS _ _).trans (Q.MG i hi)
 Ki:=E.free_map _ Q.Ki
 LP:=E.free_map _ Q.LP
end C3
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {root: Fin N}
lemma Hn {E F: Finset (Fin N ×Fin N)} (hEF: E ⊆F) {v: Fin N}
   (h: C8 M E v): C8 M F v:= by
 obtain ⟨u,w,he,hm,hv⟩:= h
 exact ⟨u,w,hEF he,hm,hv⟩
namespace Bi
variable (S: Bi G M root)
def BI (E: Finset (Fin N ×Fin N)) (hE: S.NS ⊆E)
   (hvalid:∀u v,(u,v)∈ E→ G.Adj u v)
   (hmatched:∀u v,(u,v)∈ E→ M.Adj u v→(u,v)∈ S.NS)
   (hendpoints:∀u v,(u,v)∈ E→ u∈ S.vertices∧ v∈ S.vertices): Bi G M root where
 NS:= E
 L9:= S.L9
 valid:= hvalid
 xK:= by
   intro u v he hm
   obtain ⟨P,hPl,hP,hPu,hPv⟩:= S.xK u v (hmatched u v he hm) hm
   exact ⟨P,hPl,fun i hi=> hE (hP i hi),hPu,hPv⟩
 LD:= by
   intro u v he
   obtain ⟨hu,hv⟩:= hendpoints u v he
   constructor
   · rcases S.wS u hu with hu|hu
     · exact Or.inl hu
     · exact Or.inr (Hn hE hu)
   · rcases S.wS v hv with hv|hv
     · exact Or.inl hv
     · exact Or.inr (Hn hE hv)
lemma gB (E: Finset (Fin N ×Fin N)) (hE: S.NS ⊆E)
   (hvalid:∀u v,(u,v)∈ E→ G.Adj u v)
   (hmatched:∀u v,(u,v)∈ E→ M.Adj u v→(u,v)∈ S.NS)
   (hendpoints:∀u v,(u,v)∈ E→ u∈ S.vertices∧ v∈ S.vertices):
   (S.BI E hE hvalid hmatched hendpoints).vertices= S.vertices:= by
 ext v
 constructor
 · intro hv
   rcases mem_union.mp hv with hv|hv
   · exact mem_union.mpr (Or.inl hv)
   · obtain ⟨p,hp,hv⟩:= mem_biUnion.mp hv
     have he:= hendpoints p.1 p.2 hp
     rcases mem_insert.mp hv with hv|hv
     · exact hv.symm ▸he.1
     · exact (mem_singleton.mp hv).symm ▸he.2
 · intro hv
   rcases mem_union.mp hv with hv|hv
   · exact mem_union.mpr (Or.inl hv)
   · obtain ⟨p,hp,hv⟩:= mem_biUnion.mp hv
     exact mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨p,hE hp,hv⟩))
end Bi
end Be
end
noncomputable section
namespace Be.v9
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {root: Fin N} (P: v9 G M root)
def take (k: ℕ) (hk: k≤ P.length): v9 G M root where
 length:= k
 vertex:= P.vertex
 first:= P.first
 injective:= by intro i j hi hj h;exact P.injective i j (by omega) (by omega) h
 Mu:= by intro i hi;exact P.Mu i (by omega)
 MG:= by intro i hi;exact P.MG i (by omega)
 L9:= P.L9
lemma ID (k: ℕ) (hk: k≤ P.length):(P.take k hk).M4 P:=⟨hk,fun _ _=> rfl⟩
lemma JJ (NS: Finset (Fin N ×Fin N)) (hP: P.Nv NS) (k: ℕ) (hk: k≤ P.length):
   (P.take k hk).Nv NS:= by
 intro i hi
 exact hP i (by change i< 2*k at hi;omega)
lemma GR (ell: ℕ) (labels: Fin N ×Fin N→ ℕ) (hP: P.Mq ell labels) (k: ℕ) (hk: k≤ P.length):
   (P.take k hk).Mq ell labels:= by
 refine ⟨hk.trans hP.1,?_⟩
 intro i hi
 exact hP.2 i (by change i< k at hi;omega)
lemma F5 (ell: ℕ) (labels labels': Fin N ×Fin N→ ℕ) (hP: P.Mq ell labels)
   (hm:∀a,labels' a≤ labels a): P.Mq ell labels':= by
 refine ⟨hP.1,?_⟩
 intro i hi
 exact (hm _).trans (hP.2 i hi)
def He (u v: Fin N) (i: ℕ): Fin N:=
 if i≤ 2*P.length then P.vertex i else if i= 2*P.length+1 then u else v
lemma zK (u v: Fin N) (i: ℕ) (hi: i≤ 2*P.length): P.He u v i= P.vertex i:= if_pos hi
lemma wJ (u v: Fin N): P.He u v (2*P.length+1)= u:= by simp [He]
lemma wI (u v: Fin N): P.He u v (2*P.length+2)= v:= by simp [He]
lemma jW (u v: Fin N) (hu: u∉ P.support) (hv: v∉ P.support) (hne: u≠ v)
   (i j: ℕ) (hi: i≤ 2*(P.length+1)) (hj: j≤ 2*(P.length+1))
   (heq: P.He u v i= P.He u v j): i= j:= by
 by_cases hi0: i≤ 2*P.length<;> by_cases hj0: j≤ 2*P.length
 · rw [P.zK u v i hi0,P.zK u v j hj0] at heq
   exact P.injective i j hi0 hj0 heq
 · rw [P.zK u v i hi0] at heq
   rcases (show j= 2*P.length+1∨ j= 2*P.length+2 by omega) with rfl|rfl
   · rw [P.wJ] at heq
     exact (hu (heq ▸P.mem_support i hi0)).elim
   · rw [P.wI] at heq
     exact (hv (heq ▸P.mem_support i hi0)).elim
 · rw [P.zK u v j hj0] at heq
   rcases (show i= 2*P.length+1∨ i= 2*P.length+2 by omega) with rfl|rfl
   · rw [P.wJ] at heq
     exact (hu (heq.symm ▸P.mem_support j hj0)).elim
   · rw [P.wI] at heq
     exact (hv (heq.symm ▸P.mem_support j hj0)).elim
 · rcases (show i= 2*P.length+1∨ i= 2*P.length+2 by omega) with rfl|rfl<;>
     rcases (show j= 2*P.length+1∨ j= 2*P.length+2 by omega) with rfl|rfl
   · rfl
   · exact (hne (by simpa only [P.wJ,P.wI] using heq)).elim
   · exact (hne (by simpa only [P.wJ,P.wI] using heq.symm)).elim
   · rfl
end Be.v9
end
noncomputable section
namespace Be.v9
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {alpha beta: Fin N}
   (P: v9 G M alpha) (Q: v9 G M beta)
def LK (i: ℕ): ℕ:= 2*(P.length+Q.length)+1-i
def Kv (i: ℕ): Fin N:= if i≤ 2*P.length then P.vertex i else Q.vertex (P.LK Q i)
lemma BR (i: ℕ) (hi0: 2*P.length< i) (hi: i≤ 2*(P.length+Q.length)+1):
   P.LK Q i≤ 2*Q.length:= by unfold LK;omega
lemma o5 (hd: Disjoint P.support Q.support) (i j: ℕ)
   (hi: i≤ 2*(P.length+Q.length)+1) (hj: j≤ 2*(P.length+Q.length)+1)
   (heq: P.Kv Q i= P.Kv Q j): i= j:= by
 by_cases hi0: i≤ 2*P.length<;> by_cases hj0: j≤ 2*P.length
 · rw [Kv,if_pos hi0,Kv,if_pos hj0] at heq
   exact P.injective i j hi0 hj0 heq
 · rw [Kv,if_pos hi0,Kv,if_neg hj0] at heq
   exact (disjoint_left.mp hd (heq ▸P.mem_support i hi0)
     (Q.mem_support _ (P.BR Q j (by omega) hj))).elim
 · rw [Kv,if_neg hi0,Kv,if_pos hj0] at heq
   exact (disjoint_left.mp hd (heq.symm ▸P.mem_support j hj0)
     (Q.mem_support _ (P.BR Q i (by omega) hi))).elim
 · rw [Kv,if_neg hi0,Kv,if_neg hj0] at heq
   have he:= Q.injective _ _ (P.BR Q i (by omega) hi) (P.BR Q j (by omega) hj) heq
   unfold LK at he
   omega
lemma rN (hbridge: G.Adj (P.vertex (2*P.length)) (Q.vertex (2*Q.length))) (i: ℕ)
   (hi: i≤ 2*(P.length+Q.length)): G.Adj (P.Kv Q i) (P.Kv Q (i+1)):= by
 by_cases hi0: i< 2*P.length
 · rw [Kv,if_pos (by omega: i≤ 2*P.length),Kv,if_pos (by omega: i+1≤ 2*P.length)]
   exact P.Mu i hi0
 · by_cases hi1: i= 2*P.length
   · subst i
     rw [Kv,if_pos le_rfl,Kv,if_neg (by omega:¬2*P.length+1≤ 2*P.length)]
     have he: P.LK Q (2*P.length+1)= 2*Q.length:= by unfold LK;omega
     rw [he]
     exact hbridge
   · have hi2: 2*P.length< i:= by omega
     rw [Kv,if_neg (by omega:¬i≤ 2*P.length),Kv,if_neg (by omega:¬i+1≤ 2*P.length)]
     have he: P.LK Q (i+1)+1= P.LK Q i:= by unfold LK;omega
     have hb: P.LK Q (i+1)< 2*Q.length:= by unfold LK;omega
     exact he ▸(Q.Mu _ hb).symm
lemma rO (hbridge:¬M.Adj (P.vertex (2*P.length)) (Q.vertex (2*Q.length))) (i: ℕ)
   (hi: i≤ 2*(P.length+Q.length)): M.Adj (P.Kv Q i) (P.Kv Q (i+1))↔ Odd i:= by
 by_cases hi0: i< 2*P.length
 · rw [Kv,if_pos (by omega: i≤ 2*P.length),Kv,if_pos (by omega: i+1≤ 2*P.length)]
   exact P.MG i hi0
 · by_cases hi1: i= 2*P.length
   · subst i
     rw [Kv,if_pos le_rfl,Kv,if_neg (by omega:¬2*P.length+1≤ 2*P.length)]
     have he: P.LK Q (2*P.length+1)= 2*Q.length:= by unfold LK;omega
     rw [he]
     constructor
     · exact fun h=>(hbridge h).elim
     · rintro ⟨j,hj⟩;omega
   · rw [Kv,if_neg (by omega:¬i≤ 2*P.length),Kv,if_neg (by omega:¬i+1≤ 2*P.length)]
     have he: P.LK Q (i+1)+1= P.LK Q i:= by unfold LK;omega
     have hb: P.LK Q (i+1)< 2*Q.length:= by unfold LK;omega
     have hm:=(Q.MG (P.LK Q (i+1)) hb)
     have hpar: Odd (P.LK Q (i+1))↔ Odd i:= by rw [Nat.odd_iff,Nat.odd_iff];unfold LK;omega
     rw [he] at hm
     exact (M.adj_comm _ _).trans (hm.trans hpar)
def Ac (hd: Disjoint P.support Q.support)
   (hG: G.Adj (P.vertex (2*P.length)) (Q.vertex (2*Q.length)))
   (hM:¬M.Adj (P.vertex (2*P.length)) (Q.vertex (2*Q.length))): C3 G M where
 length:= P.length+Q.length
 vertex:= P.Kv Q
 injective:= P.o5 Q hd
 Mu:= P.rN Q hG
 MG:= P.rO Q hM
 Ki:= by
   intro w
   rw [Kv,if_pos (by omega: 0≤ 2*P.length),P.first]
   exact P.L9 w
 LP:= by
   intro w
   rw [Kv,if_neg (by omega:¬2*(P.length+Q.length)+1≤ 2*P.length)]
   rw [LK,Nat.sub_self,Q.first]
   exact Q.L9 w
end Be.v9
end
noncomputable section
namespace Be
variable {N: ℕ}
lemma m9 {H M: SimpleGraph (Fin N)} (hM: Matching H M)
   (e f: Sym2 (Fin N)) (he: e∈ M.edgeSet) (hf: f∈ M.edgeSet) (v: Fin N) (hve: v∈ e) (hvf: v∈ f): e= f:= by
 by_contra hne
 have hne':(⟨e,he⟩: M.edgeSet)≠⟨f,hf⟩:= fun h=> hne (congrArg Subtype.val h)
 exact hM.2 ⟨e,he⟩ (mem_univ _) ⟨f,hf⟩ (mem_univ _) hne' v hve hvf
namespace v9
variable {G M: SimpleGraph (Fin N)} {alpha beta: Fin N} (P: v9 G M alpha)
lemma v7 (v: Fin N) (hv: v∈ P.support) (hne: v≠ alpha):
   ∃i,i< P.length∧ v∈ s(P.vertex (2*i+1),P.vertex (2*i+2)):= by
 obtain ⟨j,hj,rfl⟩:= mem_image.mp hv
 have hj': j≤ 2*P.length:= by have h:=mem_range.mp hj;omega
 have hj0: 0< j:= by
   by_contra hh
   have he: j= 0:= by omega
   exact hne (he ▸P.first)
 let i:=(j-1)/2
 have hi: i< P.length:= by dsimp [i];omega
 have he: j= 2*i+1∨ j= 2*i+2:= by dsimp [i];omega
 refine ⟨i,hi,Sym2.mem_iff.mpr ?_⟩
 exact he.elim (fun h=> Or.inl (congrArg P.vertex h)) (fun h=> Or.inr (congrArg P.vertex h))
lemma Jc (v: Fin N) (hv: v∈ P.support) (hf:∀w,¬M.Adj v w): v= alpha:= by
 by_contra hne
 obtain ⟨i,hi,hv⟩:= P.v7 v hv hne
 have hm:= P.HR i hi
 rcases Sym2.mem_iff.mp hv with hv|hv
 · exact hf (P.vertex (2*i+2)) (hv.symm ▸hm)
 · exact hf (P.vertex (2*i+1)) (hv.symm ▸hm.symm)
lemma cG (Q: v9 G M beta) (hd: Disjoint P.support Q.support)
   (i j: ℕ) (hi: i< P.length) (hj: j< Q.length):
   s(P.vertex (2*i+1),P.vertex (2*i+2))≠ s(Q.vertex (2*j+1),Q.vertex (2*j+2)):= by
 intro heq
 have hv: P.vertex (2*i+1)∈ s(Q.vertex (2*j+1),Q.vertex (2*j+2)):= by
   rw [←heq]
   exact Sym2.mem_mk_left _ _
 have hQ: P.vertex (2*i+1)∈ Q.support:= by
   rcases Sym2.mem_iff.mp hv with h|h
   · exact h.symm ▸Q.mem_support (2*j+1) (by omega)
   · exact h.symm ▸Q.mem_support (2*j+2) (by omega)
 exact disjoint_left.mp hd (P.mem_support (2*i+1) (by omega)) hQ
lemma aO {H: SimpleGraph (Fin N)} (hM: Matching H M)
   (Q: v9 G M beta) (hroot: alpha≠ beta)
   (hedges:∀i,i< P.length→∀j,j< Q.length→
     s(P.vertex (2*i+1),P.vertex (2*i+2))≠ s(Q.vertex (2*j+1),Q.vertex (2*j+2))):
   Disjoint P.support Q.support:= by
 apply disjoint_left.mpr
 intro v hvP hvQ
 have hvα: v≠ alpha:= by
   intro h
   have hh:= Q.Jc v hvQ (h.symm ▸P.L9)
   exact hroot (h.symm.trans hh)
 have hvβ: v≠ beta:= by
   intro h
   have hh:= P.Jc v hvP (h.symm ▸Q.L9)
   exact hroot (hh.symm.trans h)
 obtain ⟨i,hi,hvi⟩:= P.v7 v hvP hvα
 obtain ⟨j,hj,hvj⟩:= Q.v7 v hvQ hvβ
 have he:= m9 hM _ _ (M.mem_edgeSet.mpr (P.HR i hi))
   (M.mem_edgeSet.mpr (Q.HR j hj)) v hvi hvj
 exact hedges i hi j hj he
lemma f3 {H: SimpleGraph (Fin N)} (hM: Matching H M)
   (Q: v9 G M beta) (hroot: alpha≠ beta)
   (i j: ℕ) (hi: i< P.length) (hj: j< Q.length)
   (hrev:(P.vertex (2*i+1),P.vertex (2*i+2))=(Q.vertex (2*j+2),Q.vertex (2*j+1)))
   (hbefore:∀a,a< i→∀b,b< Q.length→
     s(P.vertex (2*a+1),P.vertex (2*a+2))≠ s(Q.vertex (2*b+1),Q.vertex (2*b+2))):
   ∃A: C3 G M,A.length= i+j+1:= by
 let L:= P.take i hi.le
 let R:= Q.take (j+1) (by omega)
 have hd: Disjoint L.support R.support:= by
   apply L.aO hM R hroot
   intro a ha b hb
   exact hbefore a ha b (by change b< j+1 at hb;omega)
 have he: P.vertex (2*i+1)= Q.vertex (2*j+2):= congrArg Prod.fst hrev
 have hG: G.Adj (L.vertex (2*L.length)) (R.vertex (2*R.length)):= by
   change G.Adj (P.vertex (2*i)) (Q.vertex (2*(j+1)))
   rw [show 2*(j+1)= 2*j+2 by omega,←he]
   exact P.Mu (2*i) (by omega)
 have hnot:¬M.Adj (L.vertex (2*L.length)) (R.vertex (2*R.length)):= by
   change ¬M.Adj (P.vertex (2*i)) (Q.vertex (2*(j+1)))
   rw [show 2*(j+1)= 2*j+2 by omega,←he]
   intro hm
   obtain ⟨k,hk⟩:=(P.MG (2*i) (by omega)).mp hm
   omega
 refine ⟨L.Ac R hd hG hnot,?_⟩
 change i+(j+1)= i+j+1
 omega
lemma bK {H: SimpleGraph (Fin N)} (hM: Matching H M)
   (Q: v9 G M beta) (hroot: alpha≠ beta)
   (hordered:∀i,i< P.length→∀j,j< Q.length→
     (P.vertex (2*i+1),P.vertex (2*i+2))≠(Q.vertex (2*j+1),Q.vertex (2*j+2)))
   (i j: ℕ) (hi: i< P.length) (hj: j< Q.length)
   (hedge: s(P.vertex (2*i+1),P.vertex (2*i+2))= s(Q.vertex (2*j+1),Q.vertex (2*j+2))):
   Nonempty (C3 G M):= by
 let F:=(range P.length).filter (fun a=>∃b,b< Q.length∧
   s(P.vertex (2*a+1),P.vertex (2*a+2))= s(Q.vertex (2*b+1),Q.vertex (2*b+2)))
 have hF: F.Nonempty:=⟨i,mem_filter.mpr ⟨mem_range.mpr hi,j,hj,hedge⟩⟩
 let k:= F.min' hF
 have hkF: k∈ F:= min'_mem F hF
 have hk: k< P.length:= mem_range.mp (mem_filter.mp hkF).1
 obtain ⟨b,hb,hkb⟩:=(mem_filter.mp hkF).2
 have hreverse:(P.vertex (2*k+1),P.vertex (2*k+2))=(Q.vertex (2*b+2),Q.vertex (2*b+1)):= by
   rcases Sym2.eq_iff.mp hkb with h|h
   · exact (hordered k hk b hb (Prod.ext h.1 h.2)).elim
   · exact Prod.ext h.1 h.2
 have hbefore:∀a,a< k→∀b,b< Q.length→
     s(P.vertex (2*a+1),P.vertex (2*a+2))≠ s(Q.vertex (2*b+1),Q.vertex (2*b+2)):= by
   intro a ha b hb heq
   have haF: a∈ F:= mem_filter.mpr ⟨mem_range.mpr (by omega),b,hb,heq⟩
   have hka: k≤ a:= min'_le F a haF
   omega
 obtain ⟨A,hA⟩:= P.f3 hM Q hroot k b hk hb hreverse hbefore
 exact ⟨A⟩
lemma cJ {H: SimpleGraph (Fin N)} (hM: Matching H M)
   (Q: v9 G M beta) (hroot: alpha≠ beta)
   (hordered:∀i,i< P.length→∀j,j< Q.length→
     (P.vertex (2*i+1),P.vertex (2*i+2))≠(Q.vertex (2*j+1),Q.vertex (2*j+2)))
   (hno:¬Nonempty (C3 G M)): Disjoint P.support Q.support:= by
 apply P.aO hM Q hroot
 intro i hi j hj heq
 exact hno (P.bK hM Q hroot hordered i j hi hj heq)
end v9
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {root: Fin N}
namespace v9
variable (P: v9 G M root)
def Nt (F: Finset (Fin N ×Fin N)): Prop:=∀i,i< P.length→ P.KA i∉ F
lemma JI (F: Finset (Fin N ×Fin N)) (hP: P.Nt F) (k: ℕ) (hk: k≤ P.length):
   (P.take k hk).Nt F:= by
 intro i hi
 exact hP i (by change i< k at hi;omega)
end v9
namespace Bi
variable (S: Bi G M root) (F: Finset (Fin N ×Fin N))
def CD: Finset (Fin N ×Fin N):= S.NS.filter (fun a=> M.Adj a.1 a.2∧
 ∃P: v9 G M root,0< P.length∧ P.Nv S.NS∧ P.Nt F∧ P.KA (P.length-1)= a)
def Ip: Finset (Fin N ×Fin N):= S.CD F ∪
 (S.NS.filter (fun a=>¬M.Adj a.1 a.2∧
   (a.1= root∨ C8 M (S.CD F) a.1)∧
   (a.2= root∨ C8 M (S.CD F) a.2)))
lemma pU: S.Ip F ⊆S.NS:= by
 intro a ha
 rcases mem_union.mp ha with ha|ha
 · exact (mem_filter.mp ha).1
 · exact (mem_filter.mp ha).1
lemma eQ (P: v9 G M root) (hP: P.Nv S.NS) (havoid: P.Nt F)
   (i: ℕ) (hi: i< P.length): P.KA i∈ S.CD F:= by
 let Q:= P.take (i+1) (by omega)
 have hQE: Q.Nv S.NS:= P.JJ S.NS hP (i+1) (by omega)
 have hQF: Q.Nt F:= P.JI F havoid (i+1) (by omega)
 have hlast: Q.KA (Q.length-1)= P.KA i:= by
   change P.KA (i+1-1)= P.KA i
   rw [Nat.add_sub_cancel]
 have he: P.KA i∈ S.NS:= hP (2*i+1) (by omega)
 exact mem_filter.mpr ⟨he,P.HR i hi,Q,by change 0< i+1;omega,hQE,hQF,hlast⟩
lemma iF (P: v9 G M root) (hP: P.Nv S.NS) (havoid: P.Nt F)
   (v: Fin N) (hv: v∈ P.support): v= root∨ C8 M (S.CD F) v:= by
 by_cases hroot: v= root
 · exact Or.inl hroot
 · obtain ⟨i,hi,hvi⟩:= P.v7 v hv hroot
   exact Or.inr ⟨P.vertex (2*i+1),P.vertex (2*i+2),S.eQ F P hP havoid i hi,
     P.HR i hi,Sym2.mem_iff.mp hvi⟩
lemma jY (P: v9 G M root) (hP: P.Nv S.NS) (havoid: P.Nt F):
   P.Nv (S.Ip F):= by
 intro i hi
 have he:= hP i hi
 by_cases hm: M.Adj (P.vertex i) (P.vertex (i+1))
 · obtain ⟨j,hj⟩:=(P.MG i hi).mp hm
   have hij: i= 2*j+1:= by omega
   have hj': j< P.length:= by omega
   have hr:= S.eQ F P hP havoid j hj'
   apply mem_union.mpr
   left
   convert hr using 1<;> congr 2<;> omega
 · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨he,hm,
     S.iF F P hP havoid _ (P.mem_support i (by omega)),
     S.iF F P hP havoid _ (P.mem_support (i+1) (by omega))⟩))
def MT: Bi G M root where
 NS:= S.Ip F
 L9:= S.L9
 valid:= fun u v h=> S.valid u v (S.pU F h)
 xK:= by
   intro u v he hm
   have hret:(u,v)∈ S.CD F:= by
     rcases mem_union.mp he with he|he
     · exact he
     · exact ((mem_filter.mp he).2.1 hm).elim
   obtain ⟨P,hPl,hPE,hPF,hLast⟩:=(mem_filter.mp hret).2.2
   have ht: 2*(P.length-1)+1= 2*P.length-1:= by omega
   have hh: 2*(P.length-1)+2= 2*P.length:= by omega
   have hx:= congrArg Prod.fst hLast
   have hy:= congrArg Prod.snd hLast
   change P.vertex (2*(P.length-1)+1)= u at hx
   change P.vertex (2*(P.length-1)+2)= v at hy
   rw [ht] at hx
   rw [hh] at hy
   exact ⟨P,hPl,S.jY F P hPE hPF,hx,hy⟩
 LD:= by
   intro u v he
   have hsub: S.CD F ⊆S.Ip F:= subset_union_left
   rcases mem_union.mp he with he|he
   · have hm:=(mem_filter.mp he).2.1
     exact ⟨Or.inr ⟨u,v,hsub he,hm,Or.inl rfl⟩,Or.inr ⟨u,v,hsub he,hm,Or.inr rfl⟩⟩
   · obtain ⟨_,_,hu,hv⟩:= mem_filter.mp he
     constructor
     · exact hu.imp id (Hn hsub)
     · exact hv.imp id (Hn hsub)
lemma pV (u v: Fin N) (hm: M.Adj u v):
   (u,v)∈ S.Ip F↔(u,v)∈ S.CD F:= by
 constructor
 · intro h
   rcases mem_union.mp h with h|h
   · exact h
   · exact ((mem_filter.mp h).2.1 hm).elim
 · exact fun h=> mem_union_left _ h
lemma lE (a: Fin N ×Fin N) (ha: a∈ S.CD F): a∉ F:= by
 obtain ⟨P,hPl,hP,hA,hLast⟩:=(mem_filter.mp ha).2.2
 have h:= hA (P.length-1) (by omega)
 rw [hLast] at h
 exact h
lemma sR (P: v9 G M root):
   P.Nv (S.Ip F)↔ P.Nv S.NS∧ P.Nt F:= by
 constructor
 · intro hP
   refine ⟨fun i hi=> S.pU F (hP i hi),?_⟩
   intro i hi
   have he: P.KA i∈ S.Ip F:= hP (2*i+1) (by omega)
   have he':=(S.pV F _ _ (P.HR i hi)).mp he
   exact S.lE F _ he'
 · rintro ⟨hP,hA⟩
   exact S.jY F P hP hA
lemma g6:(S.MT F).vertices ⊆S.vertices:= by
 intro v hv
 rcases mem_union.mp hv with hv|hv
 · exact mem_union_left _ hv
 · obtain ⟨p,hp,hv⟩:= mem_biUnion.mp hv
   have he:= S.Ft p.1 p.2 (S.pU F hp)
   rcases mem_insert.mp hv with hv|hv
   · exact hv.symm ▸he.1
   · exact (mem_singleton.mp hv).symm ▸he.2
lemma lD (K: Finset (Fin N ×Fin N)):
   (S.MT F).CD K= S.CD (F ∪K):= by
 ext a
 constructor
 · intro ha
   obtain ⟨ha,hm,P,hPl,hPE,hPK,hLast⟩:= mem_filter.mp ha
   have hInside: P.Nv (S.Ip F):= hPE
   obtain ⟨hPS,hPF⟩:=(S.sR F P).mp hInside
   refine mem_filter.mpr ⟨S.pU F ha,hm,P,hPl,hPS,?_,hLast⟩
   intro i hi hmem
   rcases mem_union.mp hmem with hf|hk
   · exact hPF i hi hf
   · exact hPK i hi hk
 · intro ha
   obtain ⟨ha,hm,P,hPl,hPE,hPK,hLast⟩:= mem_filter.mp ha
   have hPF: P.Nt F:= fun i hi h=> hPK i hi (mem_union_left _ h)
   have hP_K: P.Nt K:= fun i hi h=> hPK i hi (mem_union_right _ h)
   have hRet: a∈ S.CD F:= mem_filter.mpr ⟨ha,hm,P,hPl,hPE,hPF,hLast⟩
   exact mem_filter.mpr ⟨mem_union_left _ hRet,hm,P,hPl,S.jY F P hPE hPF,hP_K,hLast⟩
lemma lG (u v: Fin N) (hm:¬M.Adj u v):
   (u,v)∈ S.Ip F↔(u,v)∈ S.NS∧
     (u= root∨ C8 M (S.CD F) u)∧
     (v= root∨ C8 M (S.CD F) v):= by
 constructor
 · intro h
   rcases mem_union.mp h with h|h
   · exact (hm (mem_filter.mp h).2.1).elim
   · exact ⟨(mem_filter.mp h).1,(mem_filter.mp h).2.2⟩
 · rintro ⟨he,hu,hv⟩
   exact mem_union_right _ (mem_filter.mpr ⟨he,hm,hu,hv⟩)
lemma g5 (K: Finset (Fin N ×Fin N)) (hFK: F ⊆K): S.CD K ⊆S.CD F:= by
 intro a ha
 obtain ⟨he,hm,P,hPl,hPE,hPK,hLast⟩:= mem_filter.mp ha
 refine mem_filter.mpr ⟨he,hm,P,hPl,hPE,?_,hLast⟩
 intro i hi hf
 exact hPK i hi (hFK hf)
lemma sQ (K: Finset (Fin N ×Fin N)):
   (S.MT F).Ip K= S.Ip (F ∪K):= by
 have hR:= S.lD F K
 have hRsub:= S.g5 F (F ∪K) subset_union_left
 ext a
 obtain ⟨u,v⟩:= a
 by_cases hm: M.Adj u v
 · rw [(S.MT F).pV K u v hm,S.pV (F ∪K) u v hm,hR]
 · rw [(S.MT F).lG K u v hm,S.lG (F ∪K) u v hm,hR]
   constructor
   · rintro ⟨he,hu,hv⟩
     exact ⟨S.pU F he,hu,hv⟩
   · rintro ⟨he,hu,hv⟩
     refine ⟨(S.lG F u v hm).mpr ⟨he,?_,?_⟩,hu,hv⟩
     · exact hu.imp id (Hn hRsub)
     · exact hv.imp id (Hn hRsub)
lemma MA {T: Bi G M root} (h: S.NS= T.NS): S= T:= by
 cases S
 cases T
 cases h
 rfl
lemma EO (K: Finset (Fin N ×Fin N)):(S.MT F).MT K= S.MT (F ∪K):=
 ((S.MT F).MT K).MA (S.sQ F K)
lemma nT (havoid:∀P: v9 G M root,P.Nv S.NS→ P.Nt F): S.MT F= S:= by
 have hR (u v: Fin N) (he:(u,v)∈ S.NS) (hm: M.Adj u v):(u,v)∈ S.CD F:= by
   obtain ⟨P,hPl,hP,hPu,hPv⟩:= S.xK u v he hm
   have hLast: P.KA (P.length-1)=(u,v):= by
     apply Prod.ext
     · change P.vertex (2*(P.length-1)+1)= u
       rw [show 2*(P.length-1)+1= 2*P.length-1 by omega]
       exact hPu
     · change P.vertex (2*(P.length-1)+2)= v
       rw [show 2*(P.length-1)+2= 2*P.length by omega]
       exact hPv
   exact mem_filter.mpr ⟨he,hm,P,hPl,hP,havoid P hP,hLast⟩
 have hcov (v: Fin N) (hv: C8 M S.NS v): C8 M (S.CD F) v:= by
   obtain ⟨u,w,he,hm,hv⟩:= hv
   exact ⟨u,w,hR u w he hm,hm,hv⟩
 apply (S.MT F).MA
 apply Subset.antisymm (S.pU F)
 intro a ha
 obtain ⟨u,v⟩:= a
 by_cases hm: M.Adj u v
 · exact mem_union_left _ (hR u v ha hm)
 · obtain ⟨hu,hv⟩:= S.LD u v ha
   exact (S.lG F u v hm).mpr ⟨ha,hu.imp id (hcov u),hv.imp id (hcov v)⟩
lemma jH (hdis: Disjoint F S.NS): S.MT F= S:= by
 apply S.nT F
 intro P hP i hi hf
 have he: P.KA i∈ S.NS:= hP (2*i+1) (by omega)
 exact disjoint_left.mp hdis hf he
end Bi
end Be
end
noncomputable section
namespace Be.v9
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {alpha beta: Fin N}
   (P: v9 G M alpha) (Q: v9 G M beta)
def JH (j i: ℕ): ℕ:= i-2*P.length+2*j-2
def Iy (j i: ℕ): Fin N:= if i≤ 2*P.length then P.vertex i else Q.vertex (P.JH j i)
lemma yU (j: ℕ) (hj1: 1≤ j) (hj: j≤ Q.length) (i: ℕ)
   (hi0: 2*P.length< i) (hi: i≤ 2*(P.length+(Q.length+1-j))): P.JH j i≤ 2*Q.length:= by
 unfold JH
 omega
lemma AW (j: ℕ) (hj: 1≤ j) (i: ℕ) (hi: 2*P.length< i):
   P.JH j (i+1)= P.JH j i+1:= by unfold JH;omega
lemma CP (j: ℕ) (hj: 1≤ j) (i: ℕ) (hi: 2*P.length< i):
   Odd (P.JH j i)↔ Odd i:= by
 rw [Nat.odd_iff,Nat.odd_iff]
 unfold JH
 omega
lemma n0 (j: ℕ) (hj1: 1≤ j) (hj: j≤ Q.length)
   (hbridge: G.Adj (P.vertex (2*P.length)) (Q.vertex (2*j-1))) (i: ℕ)
   (hi: i< 2*(P.length+(Q.length+1-j))):
   G.Adj (P.Iy Q j i) (P.Iy Q j (i+1)):= by
 by_cases hi0: i< 2*P.length
 · rw [Iy,if_pos (by omega: i≤ 2*P.length),Iy,if_pos (by omega: i+1≤ 2*P.length)]
   exact P.Mu i hi0
 · by_cases hi1: i= 2*P.length
   · subst i
     rw [Iy,if_pos le_rfl,Iy,if_neg (by omega:¬2*P.length+1≤ 2*P.length)]
     have he: P.JH j (2*P.length+1)= 2*j-1:= by unfold JH;omega
     rw [he]
     exact hbridge
   · have hi2: 2*P.length< i:= by omega
     rw [Iy,if_neg (by omega:¬i≤ 2*P.length),Iy,if_neg (by omega:¬i+1≤ 2*P.length),P.AW j hj1 i hi2]
     apply Q.Mu
     unfold JH
     omega
lemma n1 (j: ℕ) (hj1: 1≤ j) (hj: j≤ Q.length)
   (hbridge:¬M.Adj (P.vertex (2*P.length)) (Q.vertex (2*j-1))) (i: ℕ)
   (hi: i< 2*(P.length+(Q.length+1-j))):
   M.Adj (P.Iy Q j i) (P.Iy Q j (i+1))↔ Odd i:= by
 by_cases hi0: i< 2*P.length
 · rw [Iy,if_pos (by omega: i≤ 2*P.length),Iy,if_pos (by omega: i+1≤ 2*P.length)]
   exact P.MG i hi0
 · by_cases hi1: i= 2*P.length
   · subst i
     rw [Iy,if_pos le_rfl,Iy,if_neg (by omega:¬2*P.length+1≤ 2*P.length)]
     have he: P.JH j (2*P.length+1)= 2*j-1:= by unfold JH;omega
     rw [he]
     constructor
     · exact fun h=>(hbridge h).elim
     · rintro ⟨k,hk⟩
       omega
   · have hi2: 2*P.length< i:= by omega
     rw [Iy,if_neg (by omega:¬i≤ 2*P.length),Iy,if_neg (by omega:¬i+1≤ 2*P.length),P.AW j hj1 i hi2]
     exact (Q.MG (P.JH j i) (by unfold JH;omega)).trans (P.CP j hj1 i hi2)
end Be.v9
end
noncomputable section
namespace Be.v9
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {alpha beta: Fin N}
   (P: v9 G M alpha) (Q: v9 G M beta)
def Bk (j: ℕ): Prop:=∀i k,i≤ 2*P.length→ 2*j-1≤ k→ k≤ 2*Q.length→ P.vertex i≠ Q.vertex k
lemma dH (j: ℕ) (hd: Disjoint P.support Q.support): P.Bk Q j:= by
 intro i k hi _ hk heq
 exact disjoint_left.mp hd (heq ▸P.mem_support i hi) (Q.mem_support k hk)
lemma yV (j: ℕ) (hj: 1≤ j) (i: ℕ) (hi: 2*P.length< i):
   2*j-1≤ P.JH j i:= by unfold JH;omega
lemma a9 (j: ℕ) (hj1: 1≤ j) (hj: j≤ Q.length)
   (hd: P.Bk Q j) (i k: ℕ)
   (hi: i≤ 2*(P.length+(Q.length+1-j))) (hk: k≤ 2*(P.length+(Q.length+1-j)))
   (heq: P.Iy Q j i= P.Iy Q j k): i= k:= by
 by_cases hi0: i≤ 2*P.length<;> by_cases hk0: k≤ 2*P.length
 · rw [Iy,if_pos hi0,Iy,if_pos hk0] at heq
   exact P.injective i k hi0 hk0 heq
 · rw [Iy,if_pos hi0,Iy,if_neg hk0] at heq
   exact (hd i _ hi0 (P.yV j hj1 k (by omega)) (P.yU Q j hj1 hj k (by omega) hk) heq).elim
 · rw [Iy,if_neg hi0,Iy,if_pos hk0] at heq
   exact (hd k _ hk0 (P.yV j hj1 i (by omega)) (P.yU Q j hj1 hj i (by omega) hi) heq.symm).elim
 · rw [Iy,if_neg hi0,Iy,if_neg hk0] at heq
   have hidx:= Q.injective _ _ (P.yU Q j hj1 hj i (by omega) hi) (P.yU Q j hj1 hj k (by omega) hk) heq
   unfold JH at hidx
   omega
def CO (j: ℕ) (hj1: 1≤ j) (hj: j≤ Q.length) (hd: P.Bk Q j)
   (hG: G.Adj (P.vertex (2*P.length)) (Q.vertex (2*j-1)))
   (hM:¬M.Adj (P.vertex (2*P.length)) (Q.vertex (2*j-1))): v9 G M alpha where
 length:= P.length+(Q.length+1-j)
 vertex:= P.Iy Q j
 first:= by rw [Iy,if_pos (by omega: 0≤ 2*P.length)];exact P.first
 injective:= P.a9 Q j hj1 hj hd
 Mu:= P.n0 Q j hj1 hj hG
 MG:= P.n1 Q j hj1 hj hM
 L9:= P.L9
lemma jQ (j: ℕ) (hj1: 1≤ j) (hj: j≤ Q.length) (hd: P.Bk Q j)
   (hG: G.Adj (P.vertex (2*P.length)) (Q.vertex (2*j-1)))
   (hM:¬M.Adj (P.vertex (2*P.length)) (Q.vertex (2*j-1))):
   P.M4 (P.CO Q j hj1 hj hd hG hM):= by
 refine ⟨by change P.length≤ P.length+(Q.length+1-j);omega,?_⟩
 intro i hi
 exact if_pos hi
lemma lU (j: ℕ) (hj1: 1≤ j) (hj: j≤ Q.length) (hd: P.Bk Q j)
   (hG: G.Adj (P.vertex (2*P.length)) (Q.vertex (2*j-1)))
   (hM:¬M.Adj (P.vertex (2*P.length)) (Q.vertex (2*j-1))):
   (P.CO Q j hj1 hj hd hG hM).KA P.length= Q.KA (j-1):= by
 change (P.Iy Q j (2*P.length+1),P.Iy Q j (2*P.length+2))= _
 rw [Iy,if_neg (by omega:¬2*P.length+1≤ 2*P.length),Iy,if_neg (by omega:¬2*P.length+2≤ 2*P.length)]
 have ht: P.JH j (2*P.length+1)= 2*(j-1)+1:= by unfold JH;omega
 have hh: P.JH j (2*P.length+2)= 2*(j-1)+2:= by unfold JH;omega
 rw [ht,hh]
 rfl
lemma h4 (j: ℕ) (hj1: 1≤ j) (hj: j≤ Q.length) (hd: P.Bk Q j)
   (hG: G.Adj (P.vertex (2*P.length)) (Q.vertex (2*j-1)))
   (hM:¬M.Adj (P.vertex (2*P.length)) (Q.vertex (2*j-1))) (ell: ℕ) (labels: Fin N ×Fin N→ ℕ)
   (hQ: Q.Mq ell labels) (hlabel: P.length+1< labels (Q.KA (j-1))):
   let R:= P.CO Q j hj1 hj hd hG hM
   R.Mq ell (R.Nl labels)∧ R.Nl labels (Q.KA (j-1))< labels (Q.KA (j-1)):= by
 dsimp only
 let R:= P.CO Q j hj1 hj hd hG hM
 have hQL: Q.length≤ ell:= hQ.1
 have hidx: j-1< Q.length:= by omega
 have hbound:= hQ.2 (j-1) hidx
 change labels (Q.KA (j-1))≤ j-1+1 at hbound
 have hRlen: R.length≤ ell:= by change P.length+(Q.length+1-j)≤ ell;omega
 have hRi: P.length< R.length:= by change P.length< P.length+(Q.length+1-j);omega
 refine ⟨R.AL labels ell hRlen,?_⟩
 have heq:= P.lU Q j hj1 hj hd hG hM
 rw [←heq]
 exact R.EI labels P.length hRi (by rw [heq];exact hlabel)
lemma fP (j: ℕ) (hj1: 1≤ j) (hj: j≤ Q.length) (hd: P.Bk Q j)
   (hG: G.Adj (P.vertex (2*P.length)) (Q.vertex (2*j-1)))
   (hM:¬M.Adj (P.vertex (2*P.length)) (Q.vertex (2*j-1))) (i: ℕ) (hi: i< P.length):
   (P.CO Q j hj1 hj hd hG hM).KA i= P.KA i:= by
 change (P.Iy Q j (2*i+1),P.Iy Q j (2*i+2))= _
 rw [Iy,if_pos (by omega: 2*i+1≤ 2*P.length),Iy,if_pos (by omega: 2*i+2≤ 2*P.length)]
 rfl
lemma fQ (j: ℕ) (hj1: 1≤ j) (hj: j≤ Q.length) (hd: P.Bk Q j)
   (hG: G.Adj (P.vertex (2*P.length)) (Q.vertex (2*j-1)))
   (hM:¬M.Adj (P.vertex (2*P.length)) (Q.vertex (2*j-1))) (i: ℕ) (hi: P.length≤ i):
   (P.CO Q j hj1 hj hd hG hM).KA i= Q.KA (i-P.length+j-1):= by
 change (P.Iy Q j (2*i+1),P.Iy Q j (2*i+2))= _
 rw [Iy,if_neg (by omega:¬2*i+1≤ 2*P.length),Iy,if_neg (by omega:¬2*i+2≤ 2*P.length)]
 have ht: P.JH j (2*i+1)= 2*(i-P.length+j-1)+1:= by unfold JH;omega
 have hh: P.JH j (2*i+2)= 2*(i-P.length+j-1)+2:= by unfold JH;omega
 rw [ht,hh]
 rfl
lemma p3 (j: ℕ) (hj1: 1≤ j) (hj: j≤ Q.length) (hd: P.Bk Q j)
   (hG: G.Adj (P.vertex (2*P.length)) (Q.vertex (2*j-1)))
   (hM:¬M.Adj (P.vertex (2*P.length)) (Q.vertex (2*j-1))):
   let R:= P.CO Q j hj1 hj hd hG hM
   R.KA (R.length-1)= Q.KA (Q.length-1):= by
 dsimp only
 rw [P.fQ Q j hj1 hj hd hG hM _ (by change P.length≤ P.length+(Q.length+1-j)-1;omega)]
 congr 1
 change (P.length+(Q.length+1-j)-1)-P.length+j-1= Q.length-1
 omega
lemma lT (j: ℕ) (hj1: 1≤ j) (hj: j≤ Q.length) (hd: P.Bk Q j)
   (hG: G.Adj (P.vertex (2*P.length)) (Q.vertex (2*j-1)))
   (hM:¬M.Adj (P.vertex (2*P.length)) (Q.vertex (2*j-1)))
   (E: Finset (Fin N ×Fin N)) (hP: P.Nv E)
   (hQ:∀i,2*j-1≤ i→ i< 2*Q.length→(Q.vertex i,Q.vertex (i+1))∈ E)
   (hbridge:(P.vertex (2*P.length),Q.vertex (2*j-1))∈ E):
   (P.CO Q j hj1 hj hd hG hM).Nv E:= by
 intro i hi
 change i< 2*(P.length+(Q.length+1-j)) at hi
 change (P.Iy Q j i,P.Iy Q j (i+1))∈ E
 by_cases hi0: i< 2*P.length
 · rw [Iy,if_pos (by omega: i≤ 2*P.length),Iy,if_pos (by omega: i+1≤ 2*P.length)]
   exact hP i hi0
 · by_cases hi1: i= 2*P.length
   · subst i
     rw [Iy,if_pos le_rfl,Iy,if_neg (by omega:¬2*P.length+1≤ 2*P.length)]
     have he: P.JH j (2*P.length+1)= 2*j-1:= by unfold JH;omega
     rw [he]
     exact hbridge
   · have hi2: 2*P.length< i:= by omega
     rw [Iy,if_neg (by omega:¬i≤ 2*P.length),Iy,if_neg (by omega:¬i+1≤ 2*P.length),P.AW j hj1 i hi2]
     exact hQ _ (P.yV j hj1 i hi2) (by unfold JH;omega)
end Be.v9
end
noncomputable section
namespace Be.v9
variable {N: ℕ} {G M H: SimpleGraph (Fin N)} {alpha beta: Fin N}
   (P: v9 G M alpha) (Q: v9 G M beta)
lemma n2 (j: ℕ) (hj: 1≤ j) (r: ℕ) (hrl: 2*j-1≤ r) (hru: r≤ 2*P.length):
   ∃a,j-1≤ a∧ a< P.length∧ P.vertex r∈ s(P.vertex (2*a+1),P.vertex (2*a+2)):= by
 let a:=(r-1)/2
 have ha: a< P.length:= by dsimp [a];omega
 have hal: j-1≤ a:= by dsimp [a];omega
 have he: r= 2*a+1∨ r= 2*a+2:= by dsimp [a];omega
 refine ⟨a,hal,ha,Sym2.mem_iff.mpr ?_⟩
 exact he.elim (fun h=> Or.inl (congrArg P.vertex h)) (fun h=> Or.inr (congrArg P.vertex h))
lemma aV (hM: Matching H M) (j: ℕ) (hj: 1≤ j)
   (hdis:∀a,a< P.length→∀b,j-1≤ b→ b< Q.length→
     s(P.vertex (2*a+1),P.vertex (2*a+2))≠ s(Q.vertex (2*b+1),Q.vertex (2*b+2))):
   P.Bk Q j:= by
 intro i k hi hkl hku heq
 obtain ⟨b,hbj,hb,hvk⟩:= Q.n2 j hj k hkl hku
 by_cases hi0: i= 0
 · subst i
   rw [P.first] at heq
   rw [←heq] at hvk
   have hm:= Q.HR b hb
   rcases Sym2.mem_iff.mp hvk with he|he
   · exact P.L9 _ (he.symm ▸hm)
   · exact P.L9 _ (he.symm ▸hm.symm)
 · obtain ⟨a,_,ha,hvi⟩:= P.n2 1 (by decide) i (by omega) hi
   rw [←heq] at hvk
   have hh:= Be.m9 hM _ _ (M.mem_edgeSet.mpr (P.HR a ha))
     (M.mem_edgeSet.mpr (Q.HR b hb)) _ hvi hvk
   exact hdis a ha b hbj hb hh
end Be.v9
end
noncomputable section
namespace Be.v9
variable {N: ℕ} {G M H: SimpleGraph (Fin N)} {alpha beta: Fin N}
   (P: v9 G M alpha) (Q: v9 G M beta)
lemma lS (j: ℕ) (hj1: 1≤ j) (hj: j≤ Q.length) (hd: P.Bk Q j)
   (hG: G.Adj (P.vertex (2*P.length)) (Q.vertex (2*j-1)))
   (hM:¬M.Adj (P.vertex (2*P.length)) (Q.vertex (2*j-1)))
   (F: Finset (Fin N ×Fin N)) (hP: P.Nt F)
   (hQ:∀i,j-1≤ i→ i< Q.length→ Q.KA i∉ F):
   (P.CO Q j hj1 hj hd hG hM).Nt F:= by
 intro i hi
 change i< P.length+(Q.length+1-j) at hi
 by_cases hiP: i< P.length
 · change (P.Iy Q j (2*i+1),P.Iy Q j (2*i+2))∉ F
   rw [Iy,if_pos (by omega: 2*i+1≤ 2*P.length),Iy,if_pos (by omega: 2*i+2≤ 2*P.length)]
   exact hP i hiP
 · rw [P.fQ Q j hj1 hj hd hG hM i (by omega)]
   exact hQ _ (by omega) (by omega)
lemma FR (hM: Matching H M) (i j: ℕ) (hi: i< P.length) (hj: j< Q.length)
   (heq: P.KA i= Q.KA j)
   (hbefore:∀a,a< i→∀b,j≤ b→ b< Q.length→
     s(P.vertex (2*a+1),P.vertex (2*a+2))≠ s(Q.vertex (2*b+1),Q.vertex (2*b+2)))
   (E F: Finset (Fin N ×Fin N)) (hPE: P.Nv E) (hQE: Q.Nv E) (hPF: P.Nt F)
   (hQF:∀b,j≤ b→ b< Q.length→ Q.KA b∉ F):
   ∃R: v9 G M alpha,0< R.length∧ R.Nv E∧ R.Nt F∧
     R.KA (R.length-1)= Q.KA (Q.length-1):= by
 let L:= P.take i hi.le
 have hSep: L.Bk Q (j+1):= by
   apply L.aV Q hM (j+1) (by omega)
   intro a ha b hbj hb
   exact hbefore a ha b (by omega) hb
 have htail: P.vertex (2*i+1)= Q.vertex (2*j+1):= congrArg Prod.fst heq
 have hG: G.Adj (L.vertex (2*L.length)) (Q.vertex (2*(j+1)-1)):= by
   change G.Adj (P.vertex (2*i)) (Q.vertex (2*(j+1)-1))
   rw [show 2*(j+1)-1= 2*j+1 by omega,←htail]
   exact P.Mu (2*i) (by omega)
 have hnot:¬M.Adj (L.vertex (2*L.length)) (Q.vertex (2*(j+1)-1)):= by
   change ¬M.Adj (P.vertex (2*i)) (Q.vertex (2*(j+1)-1))
   rw [show 2*(j+1)-1= 2*j+1 by omega,←htail]
   intro hm
   obtain ⟨k,hk⟩:=(P.MG (2*i) (by omega)).mp hm
   omega
 let R:= L.CO Q (j+1) (by omega) (by omega) hSep hG hnot
 have hLE: L.Nv E:= P.JJ E hPE i hi.le
 have hLF: L.Nt F:= P.JI F hPF i hi.le
 have hBridge:(L.vertex (2*L.length),Q.vertex (2*(j+1)-1))∈ E:= by
   change (P.vertex (2*i),Q.vertex (2*(j+1)-1))∈ E
   rw [show 2*(j+1)-1= 2*j+1 by omega,←htail]
   exact hPE (2*i) (by omega)
 refine ⟨R,?_,?_,?_,?_⟩
 · change 0< i+(Q.length+1-(j+1))
   omega
 · exact L.lT Q (j+1) (by omega) (by omega) hSep hG hnot E hLE (fun k _ hk=> hQE k hk) hBridge
 · exact L.lS Q (j+1) (by omega) (by omega) hSep hG hnot F hLF (fun b hb hl=> hQF b (by omega) hl)
 · exact L.p3 Q (j+1) (by omega) (by omega) hSep hG hnot
end Be.v9
end
noncomputable section
namespace Be
variable {N: ℕ}
def lZ (G M: SimpleGraph (Fin N)) (root: Fin N)
   (E F: Finset (Fin N ×Fin N)) (a: Fin N ×Fin N): Prop:=
 ∃P: v9 G M root,0< P.length∧ P.Nv E∧ P.Nt F∧ P.KA (P.length-1)= a
namespace v9
variable {G M H: SimpleGraph (Fin N)} {alpha beta: Fin N}
   (P: v9 G M alpha) (T: v9 G M beta)
lemma z0 (hM: Matching H M) (hroot: alpha≠ beta)
   (E: Finset (Fin N ×Fin N)) (hTE: T.Nv E)
   (hseparate:∀U: v9 G M beta,U.Nv E→ Disjoint P.support U.support)
   (hno:¬Nonempty (C3 G M)) (h: ℕ) (hh: h< T.length)
   (hGbridge: G.Adj (P.vertex (2*P.length)) (T.vertex (2*h+1)))
   (hMbridge:¬M.Adj (P.vertex (2*P.length)) (T.vertex (2*h+1)))
   (hblocked:¬lZ G M beta E {T.KA h} (T.KA (T.length-1))):
   ∀a,h≤ a→ a< T.length→¬lZ G M beta E {T.KA h} (T.KA a):= by
 intro a hha ha hreach
 obtain ⟨U,hUl,hUE,hUF,hLast⟩:= hreach
 let C:=(range U.length).filter (fun k=>∃b,h≤ b∧ b< T.length∧
   s(U.vertex (2*k+1),U.vertex (2*k+2))= s(T.vertex (2*b+1),T.vertex (2*b+2)))
 have hC: C.Nonempty:= by
   refine ⟨U.length-1,mem_filter.mpr ⟨mem_range.mpr (by omega),a,hha,ha,?_⟩⟩
   exact congrArg (fun p=> s(p.1,p.2)) hLast
 let k:= C.min' hC
 have hkC: k∈ C:= min'_mem C hC
 have hk: k< U.length:= mem_range.mp (mem_filter.mp hkC).1
 obtain ⟨b,hbh,hb,heq⟩:=(mem_filter.mp hkC).2
 have hbefore:∀i,i< k→∀j,h≤ j→ j< T.length→
     s(U.vertex (2*i+1),U.vertex (2*i+2))≠ s(T.vertex (2*j+1),T.vertex (2*j+2)):= by
   intro i hi j hjh hj hij
   have hiC: i∈ C:= mem_filter.mpr ⟨mem_range.mpr (by omega),j,hjh,hj,hij⟩
   have hki: k≤ i:= min'_le C i hiC
   omega
 rcases Sym2.eq_iff.mp heq with hsame|hreverse
 · have hpairs: U.KA k= T.KA b:= Prod.ext hsame.1 hsame.2
   have hbh': h< b:= by
     have hNot:= hUF k hk
     by_contra hh'
     have he: b= h:= by omega
     exact hNot (mem_singleton.mpr (hpairs.trans (congrArg T.KA he)))
   have htail:∀j,b≤ j→ j< T.length→ T.KA j∉({T.KA h}:Finset _):= by
     intro j hbj hj hmem
     have he:= T.pB j h hj hh (mem_singleton.mp hmem)
     omega
   obtain ⟨R,hRl,hRE,hRF,hRLast⟩:= U.FR T hM k b hk hb hpairs
     (fun i hi j hbj hj=> hbefore i hi j (by omega) hj) E {T.KA h} hUE hTE hUF htail
   exact hblocked ⟨R,hRl,hRE,hRF,hRLast⟩
 · have hSep:= P.dH T (h+1) (hseparate T hTE)
   have hG: G.Adj (P.vertex (2*P.length)) (T.vertex (2*(h+1)-1)):= by
     rw [show 2*(h+1)-1= 2*h+1 by omega]
     exact hGbridge
   have hnot:¬M.Adj (P.vertex (2*P.length)) (T.vertex (2*(h+1)-1)):= by
     rw [show 2*(h+1)-1= 2*h+1 by omega]
     exact hMbridge
   let A:= P.CO T (h+1) (by omega) (by omega) hSep hG hnot
   let c:= P.length+(b-h)
   have hcA: c< A.length:= by change P.length+(b-h)< P.length+(T.length+1-(h+1));omega
   have hcP: P.length≤ c:= by dsimp [c];omega
   have hcArc: A.KA c= T.KA b:= by
     rw [P.fQ T (h+1) (by omega) (by omega) hSep hG hnot c hcP]
     congr 1
     dsimp [c]
     omega
   have hrev:(U.vertex (2*k+1),U.vertex (2*k+2))=(A.vertex (2*c+2),A.vertex (2*c+1)):= by
     have hr: U.KA k=(T.KA b).swap:= Prod.ext hreverse.1 hreverse.2
     exact hr.trans (congrArg Prod.swap hcArc).symm
   have hBeforeA:∀i,i< k→∀j,j< A.length→
       s(U.vertex (2*i+1),U.vertex (2*i+2))≠ s(A.vertex (2*j+1),A.vertex (2*j+2)):= by
     intro i hi j hj hij
     by_cases hjP: j< P.length
     · have he:= congrArg (fun p=> s(p.1,p.2)) (P.fP T (h+1) (by omega) (by omega) hSep hG hnot j hjP)
       change s(A.vertex (2*j+1),A.vertex (2*j+2))= s(P.vertex (2*j+1),P.vertex (2*j+2)) at he
       rw [he] at hij
       exact U.cG P (hseparate U hUE).symm i j (by omega) hjP hij
     · let d:= j-P.length+(h+1)-1
       have hdlo: h≤ d:= by dsimp [d];omega
       have hdhi: d< T.length:= by change j< P.length+(T.length+1-(h+1)) at hj;dsimp [d];omega
       have he:= congrArg (fun p=> s(p.1,p.2)) (P.fQ T (h+1) (by omega) (by omega) hSep hG hnot j (by omega))
       change s(A.vertex (2*j+1),A.vertex (2*j+2))= s(T.vertex (2*d+1),T.vertex (2*d+2)) at he
       rw [he] at hij
       exact hbefore i hi d hdlo hdhi hij
   obtain ⟨R,hR⟩:= U.f3 hM A hroot.symm k c hk hcA hrev hBeforeA
   exact hno ⟨R⟩
end v9
end Be
end
noncomputable section
namespace Be.Bi
variable {N: ℕ} {G M H: SimpleGraph (Fin N)} {alpha beta: Fin N}
lemma GZ (S: Bi G M alpha) (v: Fin N) (hv: v∈ S.vertices):
   ∃P: v9 G M alpha,P.Nv S.NS∧ v∈ P.support:= by
 rcases S.wS v hv with hv|hv
 · let P:= v9.trivial G M alpha S.L9
   refine ⟨P,?_,?_⟩
   · intro i hi
     change i< 0 at hi
     omega
   · rw [hv]
     exact P.MU
 · obtain ⟨u,w,he,hm,hv⟩:= hv
   obtain ⟨P,hPl,hP,hPu,hPw⟩:= S.xK u w he hm
   refine ⟨P,hP,?_⟩
   rcases hv with hv|hv
   · rw [hv,←hPu]
     exact P.mem_support _ (by omega)
   · rw [hv,←hPw]
     exact P.mem_support _ le_rfl
lemma cZ (S: Bi G M alpha) (T: Bi G M beta)
   (hM: Matching H M) (hroot: alpha≠ beta)
   (howned:∀u v,(u,v)∈ S.NS→(u,v)∈ T.NS→¬M.Adj u v)
   (hno:¬Nonempty (C3 (Mv G (S.NS ∪T.NS)) M)):
   Disjoint S.vertices T.vertices:= by
 apply disjoint_left.mpr
 intro v hvS hvT
 obtain ⟨P,hP,hvP⟩:= S.GZ v hvS
 obtain ⟨Q,hQ,hvQ⟩:= T.GZ v hvT
 let P':= P.Kt (S.NS ∪T.NS) (fun i hi=> mem_union_left _ (hP i hi))
 let Q':= Q.Kt (S.NS ∪T.NS) (fun i hi=> mem_union_right _ (hQ i hi))
 have hordered:∀i,i< P'.length→∀j,j< Q'.length→
     (P'.vertex (2*i+1),P'.vertex (2*i+2))≠(Q'.vertex (2*j+1),Q'.vertex (2*j+2)):= by
   intro i hi j hj heq
   change i< P.length at hi
   change j< Q.length at hj
   change (P.vertex (2*i+1),P.vertex (2*i+2))=(Q.vertex (2*j+1),Q.vertex (2*j+2)) at heq
   have hs:= hP (2*i+1) (by omega)
   have ht:(P.vertex (2*i+1),P.vertex (2*i+2))∈ T.NS:= by
     rw [heq]
     exact hQ (2*j+1) (by omega)
   exact howned _ _ hs ht (P.HR i hi)
 have hd:= P'.cJ hM Q' hroot hordered hno
 exact disjoint_left.mp hd hvP hvQ
end Be.Bi
end
noncomputable section
namespace Be
variable {N: ℕ} {G H M: SimpleGraph (Fin N)}
namespace C3
variable (P: C3 G M)
def NM (hGH: G≤ H): C3 H M where
 length:= P.length
 vertex:= P.vertex
 injective:= P.injective
 Mu:= fun i hi=> hGH (P.Mu i hi)
 MG:= P.MG
 Ki:= P.Ki
 LP:= P.LP
end C3
namespace v9
variable {root: Fin N} (P: v9 G M root)
def NM (hGH: G≤ H): v9 H M root where
 length:= P.length
 vertex:= P.vertex
 first:= P.first
 injective:= P.injective
 Mu:= fun i hi=> hGH (P.Mu i hi)
 MG:= P.MG
 L9:= P.L9
end v9
lemma Fs (E F: Finset (Fin N ×Fin N)) (hEF: E ⊆F): Mv G E≤ Mv G F:= by
 intro u v h
 exact ⟨h.1,h.2.imp (fun h=> hEF h) (fun h=> hEF h)⟩
lemma pI (hGH: G≤ H) (hno:¬Nonempty (C3 H M)):¬Nonempty (C3 G M):= by
 rintro ⟨P⟩
 exact hno ⟨P.NM hGH⟩
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {alpha beta: Fin N}
lemma f4 (E D F: Finset (Fin N ×Fin N)) (hED: E ⊆D) (a: Fin N ×Fin N):
   lZ G M alpha E F a↔ lZ (Mv G D) M alpha E F a:= by
 constructor
 · rintro ⟨P,hPl,hP,hF,hLast⟩
   let Q:= P.Kt D (fun i hi=> hED (hP i hi))
   exact ⟨Q,hPl,hP,hF,hLast⟩
 · rintro ⟨P,hPl,hP,hF,hLast⟩
   let Q:= P.NM (show Mv G D≤ G from fun _ _ h=> h.1)
   exact ⟨Q,hPl,hP,hF,hLast⟩
structure G6 (G M: SimpleGraph (Fin N)) (alpha beta: Fin N) where
 MG: Matching G M
 left: Bi G M alpha
 right: Bi G M beta
 NX: v9 G M alpha
 inside: NX.Nv left.NS
 disjoint: Disjoint left.vertices right.vertices
 distinct: alpha≠ beta
 target: Fin N ×Fin N
 target_mem: target∈ right.NS
 EV: M.Adj target.1 target.2
 Nz: G.Adj (NX.vertex (2*NX.length)) target.1
 zV:¬M.Adj (NX.vertex (2*NX.length)) target.1
 Ck:¬Nonempty (C3 (Mv G ((left.NS ∪right.NS) ∪
   {(NX.vertex (2*NX.length),target.1),(target.1,NX.vertex (2*NX.length))})) M)
namespace G6
variable (D: G6 G M alpha beta)
def KC: Finset (Fin N ×Fin N):=(D.left.NS ∪D.right.NS) ∪
 {(D.NX.vertex (2*D.NX.length),D.target.1),(D.target.1,D.NX.vertex (2*D.NX.length))}
def H1: Finset (Fin N ×Fin N):=
 (D.right.NS.filter (fun a=> M.Adj a.1 a.2)) \D.right.CD {D.target}
lemma BX: D.left.NS ⊆D.KC:= subset_union_left.trans subset_union_left
lemma AO: D.right.NS ⊆D.KC:= subset_union_right.trans subset_union_left
lemma qT (a: Fin N ×Fin N) (ha: a∈ D.right.NS) (hm: M.Adj a.1 a.2):
   a∈ D.right.CD {D.target}↔ lZ G M beta D.right.NS {D.target} a:= by
 constructor
 · intro h
   exact (mem_filter.mp h).2.2
 · intro h
   exact mem_filter.mpr ⟨ha,hm,h⟩
lemma H2 (a: Fin N ×Fin N) (ha: a∈ D.H1):
   ∃T: v9 G M beta,0< T.length∧ T.Nv D.right.NS∧ T.KA (T.length-1)= a∧
     ∃h,h< T.length∧ T.KA h= D.target:= by
 obtain ⟨ha,hnot⟩:= mem_sdiff.mp ha
 obtain ⟨ha,hm⟩:= mem_filter.mp ha
 obtain ⟨T,hTl,hT,hTail,hHead⟩:= D.right.xK a.1 a.2 ha hm
 have hLast: T.KA (T.length-1)= a:= by
   apply Prod.ext
   · change T.vertex (2*(T.length-1)+1)= a.1
     rw [show 2*(T.length-1)+1= 2*T.length-1 by omega]
     exact hTail
   · change T.vertex (2*(T.length-1)+2)= a.2
     rw [show 2*(T.length-1)+2= 2*T.length by omega]
     exact hHead
 have hAvoid:¬T.Nt {D.target}:= by
   intro hF
   exact hnot ((D.qT a ha hm).mpr ⟨T,hTl,hT,hF,hLast⟩)
 have hcontains:∃h,h< T.length∧ T.KA h= D.target:= by
   by_contra hex
   apply hAvoid
   intro i hi hmem
   exact hex ⟨i,hi,mem_singleton.mp hmem⟩
 exact ⟨T,hTl,hT,hLast,hcontains⟩
lemma H3 (T: v9 G M beta) (hTE: T.Nv D.right.NS)
   (hTl: 0< T.length) (hLast: T.KA (T.length-1)∈ D.H1)
   (h: ℕ) (hh: h< T.length) (hTarget: T.KA h= D.target):
   ∀a,h≤ a→ a< T.length→ T.KA a∈ D.H1:= by
 let L:= D.NX.Kt D.KC (fun i hi=> D.BX (D.inside i hi))
 let Q:= T.Kt D.KC (fun i hi=> D.AO (hTE i hi))
 have hSep:∀U: v9 (Mv G D.KC) M beta,U.Nv D.right.NS→ Disjoint L.support U.support:= by
   intro U hU
   let V:= U.NM (show Mv G D.KC≤ G from fun _ _ h=> h.1)
   have hUs: V.support ⊆D.right.vertices:= D.right.EA V hU
   have hLs: L.support ⊆D.left.vertices:= D.left.EA D.NX D.inside
   exact D.disjoint.mono hLs hUs
 have hG:(Mv G D.KC).Adj (L.vertex (2*L.length)) (Q.vertex (2*h+1)):= by
   have ht: T.vertex (2*h+1)= D.target.1:= congrArg Prod.fst hTarget
   change G.Adj (D.NX.vertex (2*D.NX.length)) (T.vertex (2*h+1))∧
     ((D.NX.vertex (2*D.NX.length),T.vertex (2*h+1))∈ D.KC∨
      (T.vertex (2*h+1),D.NX.vertex (2*D.NX.length))∈ D.KC)
   rw [ht]
   exact ⟨D.Nz,Or.inl (mem_union_right _ (by simp))⟩
 have hnot:¬M.Adj (L.vertex (2*L.length)) (Q.vertex (2*h+1)):= by
   have ht: T.vertex (2*h+1)= D.target.1:= congrArg Prod.fst hTarget
   change ¬M.Adj (D.NX.vertex (2*D.NX.length)) (T.vertex (2*h+1))
   rw [ht]
   exact D.zV
 have hblocked:¬lZ (Mv G D.KC) M beta D.right.NS {Q.KA h} (Q.KA (Q.length-1)):= by
   intro hr
   have hr': lZ G M beta D.right.NS {D.target} (T.KA (T.length-1)):= by
     apply (f4 D.right.NS D.KC {D.target} D.AO _).mpr
     change lZ (Mv G D.KC) M beta D.right.NS {T.KA h} (T.KA (T.length-1)) at hr
     rw [hTarget] at hr
     exact hr
   have hforbid:=(mem_sdiff.mp hLast).2
   have he:=(mem_filter.mp (mem_sdiff.mp hLast).1).1
   exact hforbid ((D.qT _ he (T.HR _ (by omega))).mpr hr')
 have hdom:= L.z0 Q D.MG D.distinct D.right.NS hTE hSep D.Ck h hh hG hnot hblocked
 intro a hha ha
 have he: T.KA a∈ D.right.NS:= hTE (2*a+1) (by omega)
 refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨he,T.HR a ha⟩,?_⟩
 intro hr
 have hreach:=(D.qT _ he (T.HR a ha)).mp hr
 have hreach':=(f4 D.right.NS D.KC {D.target} D.AO _).mp hreach
 apply hdom a hha ha
 change lZ (Mv G D.KC) M beta D.right.NS {T.KA h} (T.KA a)
 rw [hTarget]
 exact hreach'
end G6
end Be
end
noncomputable section
namespace Be.G6
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {alpha beta: Fin N} (D: G6 G M alpha beta)
def LY: Finset (Fin N ×Fin N):= D.right.NS.filter (fun e=>
 ∃T: v9 G M beta,0< T.length∧ T.Nv D.right.NS∧
   T.KA (T.length-1)∈ D.H1∧
   ∃h,h< T.length∧ T.KA h= D.target∧
     ∃i,2*h+1≤ i∧ i< 2*T.length∧(T.vertex i,T.vertex (i+1))= e)
lemma xV: D.LY ⊆D.right.NS:= filter_subset _ _
lemma IE: D.target∈ D.H1:= by
 apply mem_sdiff.mpr
 refine ⟨mem_filter.mpr ⟨D.target_mem,D.EV⟩,?_⟩
 intro h
 exact D.right.lE {D.target} D.target h (mem_singleton_self _)
lemma Gd (e: Fin N ×Fin N) (he: e∈ D.H1): e∈ D.LY:= by
 obtain ⟨T,hTl,hTE,hLast,h,hh,hTarget⟩:= D.H2 e he
 have hE: e∈ D.right.NS:=(mem_filter.mp (mem_sdiff.mp he).1).1
 apply mem_filter.mpr
 refine ⟨hE,T,hTl,hTE,?_,h,hh,hTarget,2*(T.length-1)+1,?_,?_,?_⟩
 · rw [hLast]
   exact he
 · omega
 · omega
 · simpa only [v9.KA,Nat.add_assoc] using hLast
lemma uW (e: Fin N ×Fin N) (he: e∈ D.LY) (hm: M.Adj e.1 e.2): e∈ D.H1:= by
 obtain ⟨_,T,hTl,hTE,hLast,h,hh,hTarget,i,hi0,hi,heq⟩:= mem_filter.mp he
 have hmi: M.Adj (T.vertex i) (T.vertex (i+1)):= by
   have hfst: T.vertex i= e.1:= congrArg Prod.fst heq
   have hsnd: T.vertex (i+1)= e.2:= congrArg Prod.snd heq
   rw [hfst,hsnd]
   exact hm
 obtain ⟨j,hj⟩:=(T.MG i hi).mp hmi
 have hij: i= 2*j+1:= by omega
 have hjh: h≤ j:= by omega
 have hjT: j< T.length:= by omega
 have hmem:= D.H3 T hTE hTl hLast h hh hTarget j hjh hjT
 have heArc: T.KA j= e:= by
   change (T.vertex (2*j+1),T.vertex (2*j+2))= e
   rw [hij] at heq
   exact heq
 exact heArc ▸hmem
def Ne: Finset (Fin N ×Fin N):=(D.left.NS ∪
 {(D.NX.vertex (2*D.NX.length),D.target.1),(D.target.1,D.NX.vertex (2*D.NX.length))}) ∪D.LY
lemma BY: D.left.NS ⊆D.Ne:= subset_union_left.trans subset_union_left
lemma Au: D.LY ⊆D.Ne:= subset_union_right
lemma En: D.Ne ⊆D.KC:= by
 intro a ha
 rcases mem_union.mp ha with ha|ha
 · rcases mem_union.mp ha with ha|ha
   · exact D.BX ha
   · exact mem_union_right _ ha
 · exact D.AO (D.xV ha)
lemma Dp:(D.NX.vertex (2*D.NX.length),D.target.1)∈ D.Ne:=
 mem_union_left _ (mem_union_right _ (by simp))
lemma EW: D.target∈ D.Ne:= D.Au (D.Gd D.target D.IE)
end Be.G6
end
noncomputable section
namespace Be.G6
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {alpha beta: Fin N} (D: G6 G M alpha beta)
lemma Gs (T: v9 G M beta) (hTl: 0< T.length) (hTE: T.Nv D.right.NS)
   (hLast: T.KA (T.length-1)∈ D.H1) (h: ℕ) (hh: h< T.length)
   (hTarget: T.KA h= D.target):
   ∃R: v9 G M alpha,0< R.length∧ R.Nv D.Ne∧ R.KA (R.length-1)= T.KA (T.length-1):= by
 have hd: Disjoint D.NX.support T.support:= D.disjoint.mono (D.left.EA D.NX D.inside) (D.right.EA T hTE)
 have hSep:= D.NX.dH T (h+1) hd
 have ht: T.vertex (2*h+1)= D.target.1:= congrArg Prod.fst hTarget
 have hG: G.Adj (D.NX.vertex (2*D.NX.length)) (T.vertex (2*(h+1)-1)):= by
   rw [show 2*(h+1)-1= 2*h+1 by omega,ht]
   exact D.Nz
 have hnot:¬M.Adj (D.NX.vertex (2*D.NX.length)) (T.vertex (2*(h+1)-1)):= by
   rw [show 2*(h+1)-1= 2*h+1 by omega,ht]
   exact D.zV
 let R:= D.NX.CO T (h+1) (by omega) (by omega) hSep hG hnot
 have hP: D.NX.Nv D.Ne:= fun i hi=> D.BY (D.inside i hi)
 have hQ:∀i,2*(h+1)-1≤ i→ i< 2*T.length→(T.vertex i,T.vertex (i+1))∈ D.Ne:= by
   intro i hlo hi
   apply D.Au
   exact mem_filter.mpr ⟨hTE i hi,T,hTl,hTE,hLast,h,hh,hTarget,i,by omega,hi,rfl⟩
 have hb:(D.NX.vertex (2*D.NX.length),T.vertex (2*(h+1)-1))∈ D.Ne:= by
   rw [show 2*(h+1)-1= 2*h+1 by omega,ht]
   exact D.Dp
 refine ⟨R,?_,D.NX.lT T (h+1) (by omega) (by omega) hSep hG hnot D.Ne hP hQ hb,?_⟩
 · change 0< D.NX.length+(T.length+1-(h+1))
   omega
 · exact D.NX.p3 T (h+1) (by omega) (by omega) hSep hG hnot
lemma Cd (a: Fin N ×Fin N) (ha: a∈ D.H1):
   ∃R: v9 G M alpha,0< R.length∧ R.Nv D.Ne∧ R.KA (R.length-1)= a:= by
 obtain ⟨T,hTl,hTE,hLast,h,hh,hTarget⟩:= D.H2 a ha
 have hLD: T.KA (T.length-1)∈ D.H1:= hLast.symm ▸ha
 obtain ⟨R,hRl,hR,hRa⟩:= D.Gs T hTl hTE hLD h hh hTarget
 exact ⟨R,hRl,hR,hRa.trans hLast⟩
lemma uX (T: v9 G M beta) (hTl: 0< T.length) (hTE: T.Nv D.right.NS)
   (hLast: T.KA (T.length-1)∈ D.H1) (h: ℕ) (hh: h< T.length)
   (hTarget: T.KA h= D.target) (r: ℕ) (hrl: 2*h+1≤ r) (hru: r≤ 2*T.length):
   C8 M D.Ne (T.vertex r):= by
 obtain ⟨a,hal,ha,hva⟩:= T.n2 (h+1) (by omega) r (by omega) hru
 have hD:= D.H3 T hTE hTl hLast h hh hTarget a (by omega) ha
 have hNew:= D.Au (D.Gd _ hD)
 exact ⟨T.vertex (2*a+1),T.vertex (2*a+2),hNew,T.HR a ha,Sym2.mem_iff.mp hva⟩
lemma Cc (e: Fin N ×Fin N) (he: e∈ D.LY):
   C8 M D.Ne e.1∧ C8 M D.Ne e.2:= by
 obtain ⟨_,T,hTl,hTE,hLast,h,hh,hTarget,i,hi0,hi,heq⟩:= mem_filter.mp he
 constructor
 · rw [←congrArg Prod.fst heq]
   exact D.uX T hTl hTE hLast h hh hTarget i hi0 (by omega)
 · rw [←congrArg Prod.snd heq]
   exact D.uX T hTl hTE hLast h hh hTarget (i+1) (by omega) (by omega)
end Be.G6
end
noncomputable section
namespace Be.G6
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {alpha beta: Fin N} (D: G6 G M alpha beta)
lemma LZ:∀u v,(u,v)∈ D.Ne→ G.Adj u v:= by
 intro u v he
 rcases mem_union.mp he with he|he
 · rcases mem_union.mp he with he|he
   · exact D.left.valid u v he
   · simp only [mem_insert,mem_singleton] at he
     rcases he with he|he
     · obtain ⟨hu,hv⟩:= Prod.mk.inj he
       rw [hu,hv]
       exact D.Nz
     · obtain ⟨hu,hv⟩:= Prod.mk.inj he
       rw [hu,hv]
       exact D.Nz.symm
 · exact D.right.valid u v (D.xV he)
lemma Gh:∀u v,(u,v)∈ D.Ne→ M.Adj u v→
   ∃P: v9 G M alpha,0< P.length∧ P.Nv D.Ne∧
     P.vertex (2*P.length-1)= u∧ P.vertex (2*P.length)= v:= by
 intro u v he hm
 rcases mem_union.mp he with he|he
 · rcases mem_union.mp he with he|he
   · obtain ⟨P,hPl,hPE,hPu,hPv⟩:= D.left.xK u v he hm
     exact ⟨P,hPl,fun i hi=> D.BY (hPE i hi),hPu,hPv⟩
   · simp only [mem_insert,mem_singleton] at he
     rcases he with he|he
     · obtain ⟨hu,hv⟩:= Prod.mk.inj he
       rw [hu,hv] at hm
       exact (D.zV hm).elim
     · obtain ⟨hu,hv⟩:= Prod.mk.inj he
       rw [hu,hv] at hm
       exact (D.zV hm.symm).elim
 · have hD:= D.uW (u,v) he hm
   obtain ⟨P,hPl,hPE,hLast⟩:= D.Cd (u,v) hD
   have ht: 2*(P.length-1)+1= 2*P.length-1:= by omega
   have hh: 2*(P.length-1)+2= 2*P.length:= by omega
   have hx:= congrArg Prod.fst hLast
   have hy:= congrArg Prod.snd hLast
   change P.vertex (2*(P.length-1)+1)= u at hx
   change P.vertex (2*(P.length-1)+2)= v at hy
   rw [ht] at hx
   rw [hh] at hy
   exact ⟨P,hPl,hPE,hx,hy⟩
lemma Gg:∀u v,(u,v)∈ D.Ne→
   (u= alpha∨ C8 M D.Ne u)∧(v= alpha∨ C8 M D.Ne v):= by
 have old (w: Fin N) (hw: w∈ D.left.vertices): w= alpha∨ C8 M D.Ne w:= by
   rcases D.left.wS w hw with hw|hw
   · exact Or.inl hw
   · exact Or.inr (Hn D.BY hw)
 have hhead: D.NX.vertex (2*D.NX.length)∈ D.left.vertices:=
   D.left.EA D.NX D.inside (D.NX.mem_support _ le_rfl)
 have ht: C8 M D.Ne D.target.1:=⟨D.target.1,D.target.2,D.EW,D.EV,Or.inl rfl⟩
 intro u v he
 rcases mem_union.mp he with he|he
 · rcases mem_union.mp he with he|he
   · exact ⟨old u (D.left.Ft u v he).1,old v (D.left.Ft u v he).2⟩
   · simp only [mem_insert,mem_singleton] at he
     rcases he with he|he
     · obtain ⟨hu,hv⟩:= Prod.mk.inj he
       rw [hu,hv]
       exact ⟨old _ hhead,Or.inr ht⟩
     · obtain ⟨hu,hv⟩:= Prod.mk.inj he
       rw [hu,hv]
       exact ⟨Or.inr ht,old _ hhead⟩
 · have he':= D.Cc (u,v) he
   exact ⟨Or.inr he'.1,Or.inr he'.2⟩
def JM: Bi G M alpha where
 NS:= D.Ne
 L9:= D.left.L9
 valid:= D.LZ
 xK:= D.Gh
 LD:= D.Gg
abbrev remaining: Bi G M beta:= D.right.MT {D.target}
lemma p9: Disjoint D.JM.vertices D.remaining.vertices:= by
 apply Bi.cZ D.JM D.remaining D.MG D.distinct
 · intro u v heL heR hm
   change (u,v)∈ D.Ne at heL
   change (u,v)∈ D.right.Ip {D.target} at heR
   rcases mem_union.mp heL with heL|heL
   · rcases mem_union.mp heL with heL|heL
     · have huL:=(D.left.Ft u v heL).1
       have huR:=(D.right.Ft u v (D.right.pU {D.target} heR)).1
       exact disjoint_left.mp D.disjoint huL huR
     · simp only [mem_insert,mem_singleton] at heL
       rcases heL with heL|heL
       · obtain ⟨hu,hv⟩:= Prod.mk.inj heL
         rw [hu,hv] at hm
         exact D.zV hm
       · obtain ⟨hu,hv⟩:= Prod.mk.inj heL
         rw [hu,hv] at hm
         exact D.zV hm.symm
   · have hMoved:= D.uW (u,v) heL hm
     have hRet:=(D.right.pV {D.target} u v hm).mp heR
     exact (mem_sdiff.mp hMoved).2 hRet
 · have hsub: D.JM.NS ∪D.remaining.NS ⊆D.KC:= by
     intro a ha
     rcases mem_union.mp ha with ha|ha
     · exact D.En ha
     · exact D.AO (D.right.pU {D.target} ha)
   exact pI (Fs _ _ hsub) D.Ck
end Be.G6
end
noncomputable section
namespace Be.G6
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {alpha beta: Fin N} (D: G6 G M alpha beta)
lemma Ci (e: Fin N ×Fin N) (hm: M.Adj e.1 e.2):
   e∈ D.Ne↔ e∈ D.left.NS∨ e∈ D.H1:= by
 constructor
 · intro he
   rcases mem_union.mp he with he|he
   · rcases mem_union.mp he with he|he
     · exact Or.inl he
     · simp only [mem_insert,mem_singleton] at he
       rcases he with he|he
       · have hfst:= congrArg Prod.fst he
         have hsnd:= congrArg Prod.snd he
         rw [hfst,hsnd] at hm
         exact (D.zV hm).elim
       · have hfst:= congrArg Prod.fst he
         have hsnd:= congrArg Prod.snd he
         rw [hfst,hsnd] at hm
         exact (D.zV hm.symm).elim
   · exact Or.inr (D.uW e he hm)
 · rintro (he|he)
   · exact D.BY he
   · exact D.Au (D.Gd e he)
lemma xJ (e: Fin N ×Fin N) (hm: M.Adj e.1 e.2):
   (e∈ D.JM.NS∨ e∈ D.remaining.NS)↔(e∈ D.left.NS∨ e∈ D.right.NS):= by
 constructor
 · rintro (he|he)
   · rcases (D.Ci e hm).mp he with he|he
     · exact Or.inl he
     · exact Or.inr (mem_filter.mp (mem_sdiff.mp he).1).1
   · exact Or.inr (D.right.pU {D.target} he)
 · rintro (he|he)
   · exact Or.inl (D.BY he)
   · by_cases hr: e∈ D.right.CD {D.target}
     · exact Or.inr (mem_union_left _ hr)
     · exact Or.inl (D.Au (D.Gd e (mem_sdiff.mpr ⟨mem_filter.mpr ⟨he,hm⟩,hr⟩)))
lemma An (u v: Fin N) (he:(u,v)∈ D.KC):
   u∈ D.left.vertices ∪D.right.vertices∧ v∈ D.left.vertices ∪D.right.vertices:= by
 have hhead:= D.left.EA D.NX D.inside (D.NX.mem_support (2*D.NX.length) le_rfl)
 have htail:=(D.right.Ft D.target.1 D.target.2 D.target_mem).1
 rcases mem_union.mp he with he|he
 · rcases mem_union.mp he with he|he
   · have hh:= D.left.Ft u v he
     exact ⟨mem_union_left _ hh.1,mem_union_left _ hh.2⟩
   · have hh:= D.right.Ft u v he
     exact ⟨mem_union_right _ hh.1,mem_union_right _ hh.2⟩
 · simp only [mem_insert,mem_singleton] at he
   rcases he with he|he
   · obtain ⟨hu,hv⟩:= Prod.mk.inj he
     rw [hu,hv]
     exact ⟨mem_union_left _ hhead,mem_union_right _ htail⟩
   · obtain ⟨hu,hv⟩:= Prod.mk.inj he
     rw [hu,hv]
     exact ⟨mem_union_right _ htail,mem_union_left _ hhead⟩
lemma r4: D.JM.vertices ⊆D.left.vertices ∪D.right.vertices:= by
 intro v hv
 rcases mem_union.mp hv with hv|hv
 · rw [mem_singleton.mp hv]
   exact mem_union_left _ D.left.MU
 · obtain ⟨p,hp,hv⟩:= mem_biUnion.mp hv
   have he:= D.An p.1 p.2 (D.En hp)
   rcases mem_insert.mp hv with hv|hv
   · exact hv.symm ▸he.1
   · exact (mem_singleton.mp hv).symm ▸he.2
lemma x0: D.left.vertices ⊆D.JM.vertices:= by
 intro v hv
 rcases mem_union.mp hv with hv|hv
 · exact mem_union_left _ hv
 · obtain ⟨p,hp,hv⟩:= mem_biUnion.mp hv
   exact mem_union_right _ (mem_biUnion.mpr ⟨p,D.BY hp,hv⟩)
lemma v8: D.JM.vertices ∪D.remaining.vertices= D.left.vertices ∪D.right.vertices:= by
 apply Subset.antisymm
 · intro v hv
   rcases mem_union.mp hv with hv|hv
   · exact D.r4 hv
   · exact mem_union_right _ (D.right.g6 {D.target} hv)
 · intro v hv
   rcases mem_union.mp hv with hv|hv
   · exact mem_union_left _ (D.x0 hv)
   · rcases D.right.wS v hv with hv|hv
     · rw [hv]
       exact mem_union_right _ D.remaining.MU
     · obtain ⟨u,w,he,hm,hv⟩:= hv
       have hp:=(D.xJ (u,w) hm).mpr (Or.inr he)
       rcases hp with hp|hp
       · have hv':= D.JM.Ft u w hp
         rcases hv with hv|hv
         · exact mem_union_left _ (hv.symm ▸hv'.1)
         · exact mem_union_left _ (hv.symm ▸hv'.2)
       · have hv':= D.remaining.Ft u w hp
         rcases hv with hv|hv
         · exact mem_union_right _ (hv.symm ▸hv'.1)
         · exact mem_union_right _ (hv.symm ▸hv'.2)
end Be.G6
end
noncomputable section
namespace Be.Bi
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {root: Fin N} (S: Bi G M root)
   (u v: Fin N) (hu: u∈ S.vertices) (hv: v∈ S.vertices) (hG: G.Adj u v) (hM:¬M.Adj u v)
include hu hv hG hM in
def zH: Bi G M root:=
 S.BI (S.NS ∪{(u,v)}) subset_union_left
   (by
     intro a b he
     rcases mem_union.mp he with he|he
     · exact S.valid a b he
     · obtain ⟨ha,hb⟩:= Prod.mk.inj (mem_singleton.mp he)
       rw [ha,hb];exact hG)
   (by
     intro a b he hm
     rcases mem_union.mp he with he|he
     · exact he
     · obtain ⟨ha,hb⟩:= Prod.mk.inj (mem_singleton.mp he)
       rw [ha,hb] at hm;exact (hM hm).elim)
   (by
     intro a b he
     rcases mem_union.mp he with he|he
     · exact S.Ft a b he
     · obtain ⟨ha,hb⟩:= Prod.mk.inj (mem_singleton.mp he)
       rw [ha,hb];exact ⟨hu,hv⟩)
include hu hv hG hM in
lemma eP:(S.zH u v hu hv hG hM).vertices= S.vertices:=
 S.gB _ _ _ _ _
end Be.Bi
end
noncomputable section
namespace Be.Bi
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {root: Fin N} (S: Bi G M root)
   (E: Finset (Fin N ×Fin N)) (hE: E ⊆S.NS)
   (hmatched:∀u v,(u,v)∈ S.NS→ M.Adj u v→(u,v)∈ E)
   (hreach:∀u v,(u,v)∈ E→ M.Adj u v→
     ∃P: v9 G M root,0< P.length∧ P.Nv E∧
       P.vertex (2*P.length-1)= u∧ P.vertex (2*P.length)= v)
include hmatched in
lemma Ho (v: Fin N) (hv: C8 M S.NS v): C8 M E v:= by
 obtain ⟨u,w,he,hm,hv⟩:= hv
 exact ⟨u,w,hmatched u w he hm,hm,hv⟩
def GV: Bi G M root where
 NS:= E
 L9:= S.L9
 valid:= fun u v he=> S.valid u v (hE he)
 xK:= hreach
 LD:= by
   intro u v he
   obtain ⟨hu,hv⟩:= S.LD u v (hE he)
   exact ⟨hu.imp id (S.Ho E hmatched u),hv.imp id (S.Ho E hmatched v)⟩
lemma lX:(S.GV E hE hmatched hreach).vertices= S.vertices:= by
 apply Subset.antisymm
 · intro v hv
   rcases mem_union.mp hv with hv|hv
   · exact mem_union_left _ hv
   · obtain ⟨e,he,hv⟩:= mem_biUnion.mp hv
     exact mem_union_right _ (mem_biUnion.mpr ⟨e,hE he,hv⟩)
 · intro v hv
   rcases S.wS v hv with hv|hv
   · rw [hv]
     exact (S.GV E hE hmatched hreach).MU
   · obtain ⟨u,w,he,hm,hv⟩:= hv
     have hh:=(S.GV E hE hmatched hreach).Ft u w (hmatched u w he hm)
     exact hv.elim (fun h=> h ▸hh.1) (fun h=> h ▸hh.2)
end Be.Bi
end
noncomputable section
namespace Be.G6
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {alpha beta: Fin N} (D: G6 G M alpha beta)
def Jb: Finset (Fin N ×Fin N):=
 (D.left.NS ∪{(D.NX.vertex (2*D.NX.length),D.target.1)}) ∪D.LY
lemma DP: D.Jb ⊆D.Ne:= by
 intro e he
 rcases mem_union.mp he with he|he
 · rcases mem_union.mp he with he|he
   · exact D.BY he
   · rw [mem_singleton.mp he]
     exact D.Dp
 · exact D.Au he
lemma BO (u v: Fin N) (he:(u,v)∈ D.Ne) (hm: M.Adj u v):(u,v)∈ D.Jb:= by
 rcases (D.Ci (u,v) hm).mp he with he|he
 · exact mem_union_left _ (mem_union_left _ he)
 · exact mem_union_right _ (D.Gd _ he)
lemma Ht (T: v9 G M beta) (hTl: 0< T.length) (hTE: T.Nv D.right.NS)
   (hLast: T.KA (T.length-1)∈ D.H1) (h: ℕ) (hh: h< T.length)
   (hTarget: T.KA h= D.target):
   ∃R: v9 G M alpha,0< R.length∧ R.Nv D.Jb∧
     R.KA (R.length-1)= T.KA (T.length-1):= by
 have hd: Disjoint D.NX.support T.support:= D.disjoint.mono
   (D.left.EA D.NX D.inside) (D.right.EA T hTE)
 have hSep:= D.NX.dH T (h+1) hd
 have ht: T.vertex (2*h+1)= D.target.1:= congrArg Prod.fst hTarget
 have hG: G.Adj (D.NX.vertex (2*D.NX.length)) (T.vertex (2*(h+1)-1)):= by
   rw [show 2*(h+1)-1= 2*h+1 by omega,ht]
   exact D.Nz
 have hnot:¬M.Adj (D.NX.vertex (2*D.NX.length)) (T.vertex (2*(h+1)-1)):= by
   rw [show 2*(h+1)-1= 2*h+1 by omega,ht]
   exact D.zV
 let R:= D.NX.CO T (h+1) (by omega) (by omega) hSep hG hnot
 have hP: D.NX.Nv D.Jb:= fun i hi=> mem_union_left _ (mem_union_left _ (D.inside i hi))
 have hQ:∀i,2*(h+1)-1≤ i→ i< 2*T.length→(T.vertex i,T.vertex (i+1))∈ D.Jb:= by
   intro i hlo hi
   apply mem_union_right
   exact mem_filter.mpr ⟨hTE i hi,T,hTl,hTE,hLast,h,hh,hTarget,i,by omega,hi,rfl⟩
 have hb:(D.NX.vertex (2*D.NX.length),T.vertex (2*(h+1)-1))∈ D.Jb:= by
   rw [show 2*(h+1)-1= 2*h+1 by omega,ht]
   exact mem_union_left _ (mem_union_right _ (mem_singleton_self _))
 refine ⟨R,?_,D.NX.lT T (h+1) (by omega) (by omega) hSep hG hnot D.Jb hP hQ hb,?_⟩
 · change 0< D.NX.length+(T.length+1-(h+1))
   omega
 · exact D.NX.p3 T (h+1) (by omega) (by omega) hSep hG hnot
lemma w5 (u v: Fin N) (he:(u,v)∈ D.Jb) (hm: M.Adj u v):
   ∃P: v9 G M alpha,0< P.length∧ P.Nv D.Jb∧
     P.vertex (2*P.length-1)= u∧ P.vertex (2*P.length)= v:= by
 rcases (D.Ci (u,v) hm).mp (D.DP he) with he|he
 · obtain ⟨P,hPl,hP,hPu,hPv⟩:= D.left.xK u v he hm
   exact ⟨P,hPl,fun i hi=> mem_union_left _ (mem_union_left _ (hP i hi)),hPu,hPv⟩
 · obtain ⟨T,hTl,hTE,hLast,h,hh,hTarget⟩:= D.H2 (u,v) he
   obtain ⟨P,hPl,hP,hEnd⟩:= D.Ht T hTl hTE (hLast.symm ▸he) h hh hTarget
   have heq:= hEnd.trans hLast
   have ht: P.vertex (2*(P.length-1)+1)= u:= congrArg Prod.fst heq
   have hv: P.vertex (2*(P.length-1)+2)= v:= congrArg Prod.snd heq
   rw [show 2*(P.length-1)+1= 2*P.length-1 by omega] at ht
   rw [show 2*(P.length-1)+2= 2*P.length by omega] at hv
   exact ⟨P,hPl,hP,ht,hv⟩
def t3: Bi G M alpha:=
 D.JM.GV D.Jb D.DP D.BO D.w5
lemma z4: D.t3.vertices= D.JM.vertices:=
 D.JM.lX D.Jb D.DP D.BO D.w5
lemma q5: D.left.NS ⊆D.t3.NS:= subset_union_left.trans subset_union_left
lemma t4:(D.NX.vertex (2*D.NX.length),D.target.1)∈ D.t3.NS:=
 mem_union_left _ (mem_union_right _ (mem_singleton_self _))
lemma t5: D.target∈ D.t3.NS:= mem_union_right _ (D.Gd _ D.IE)
lemma z3: Disjoint D.t3.vertices D.remaining.vertices:= by
 rw [D.z4]
 exact D.p9
lemma dY: D.t3.vertices ∪D.remaining.vertices= D.left.vertices ∪D.right.vertices:= by
 rw [D.z4]
 exact D.v8
lemma e3 (e: Fin N ×Fin N) (hm: M.Adj e.1 e.2):
   (e∈ D.t3.NS∨ e∈ D.remaining.NS)↔(e∈ D.left.NS∨ e∈ D.right.NS):= by
 constructor
 · intro h
   exact (D.xJ e hm).mp (h.imp (fun he=> D.DP he) id)
 · intro h
   exact ((D.xJ e hm).mpr h).imp (fun he=> D.BO e.1 e.2 he hm) id
end Be.G6
end
noncomputable section
namespace Be.v9
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {root: Fin N} (P: v9 G M root)
lemma AY (n: ℕ) (hn: n< P.length) (E: Finset (Fin N ×Fin N))
   (hold:(P.take n (by omega)).Nv E)
   (hbridge:(P.vertex (2*n),P.vertex (2*n+1))∈ E)
   (hmatched: P.KA n∈ E):(P.take (n+1) (by omega)).Nv E:= by
 intro i hi
 change i< 2*(n+1) at hi
 change (P.vertex i,P.vertex (i+1))∈ E
 by_cases hiold: i< 2*n
 · exact hold i hiold
 · rcases (show i= 2*n∨ i= 2*n+1 by omega) with rfl|rfl
   · exact hbridge
   · convert hmatched using 1<;> congr 2<;> omega
lemma zV (n: ℕ) (hn: n< P.length):¬M.Adj (P.vertex (2*n)) (P.vertex (2*n+1)):= by
 intro hm
 have hh:=(P.MG (2*n) (by omega)).mp hm
 obtain ⟨j,hj⟩:= hh
 omega
end Be.v9
end
noncomputable section
namespace Be
variable {N: ℕ}
def GQ (E: Finset (Fin N ×Fin N)): Finset (Fin N ×Fin N):= E ∪E.image Prod.swap
lemma xP (E: Finset (Fin N ×Fin N)) (u v: Fin N):
   (u,v)∈ GQ E↔(u,v)∈ E∨(v,u)∈ E:= by
 simp [GQ,mem_image,Prod.ext_iff,and_assoc]
lemma lW (E: Finset (Fin N ×Fin N)): E ⊆GQ E:= subset_union_left
lemma jX (G: SimpleGraph (Fin N)) (E: Finset (Fin N ×Fin N)):
   Mv G (GQ E)= Mv G E:= by
 ext u v
 change (G.Adj u v∧((u,v)∈ GQ E∨(v,u)∈ GQ E))↔ _
 rw [xP,xP]
 change (G.Adj u v∧(((u,v)∈ E∨(v,u)∈ E)∨((v,u)∈ E∨(u,v)∈ E)))↔
   (G.Adj u v∧((u,v)∈ E∨(v,u)∈ E))
 tauto
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {alpha beta: Fin N}
lemma sZ (hM: Matching G M) (A: Bi G M alpha) (B: Bi G M beta)
   (P: v9 G M alpha) (n: ℕ) (hn: n< P.length)
   (E: Finset (Fin N ×Fin N))
   (hAE: A.NS ⊆E) (hBE: B.NS ⊆E) (hPE: P.Nv E)
   (hNo:¬Nonempty (C3 (Mv G E) M))
   (hdis: Disjoint A.vertices B.vertices)
   (hP:(P.take n (by omega)).Nv A.NS)
   (he: P.KA n∈ A.NS ∪B.NS):
   ∃(A': Bi G M alpha) (B': Bi G M beta),
     B'= B.MT {P.KA n}∧ A.NS ⊆A'.NS∧
     A'.NS ⊆E∧ B'.NS ⊆E∧ Disjoint A'.vertices B'.vertices∧
     A'.vertices ∪B'.vertices= A.vertices ∪B.vertices∧
     (∀e,M.Adj e.1 e.2→(e∈ A'.NS∨ e∈ B'.NS↔ e∈ A.NS∨ e∈ B.NS))∧
     (P.take (n+1) (by omega)).Nv A'.NS:= by
 have hbridge:= P.Mu (2*n) (by omega)
 have hnot:= P.zV n hn
 have hpair:(P.vertex (2*n),P.vertex (2*n+1))∈ E:= hPE (2*n) (by omega)
 have hdistinct: alpha≠ beta:= by
   intro h
   exact disjoint_left.mp hdis A.MU (h ▸B.MU)
 by_cases hleft: P.KA n∈ A.NS
 · have hu: P.vertex (2*n)∈ A.vertices:=
     A.EA (P.take n (by omega)) hP ((P.take n (by omega)).mem_support (2*n) le_rfl)
   have hv: P.vertex (2*n+1)∈ A.vertices:=(A.Ft _ _ hleft).1
   let A':= A.zH _ _ hu hv hbridge hnot
   have hsame: A'.vertices= A.vertices:= A.eP _ _ hu hv hbridge hnot
   have htarget: P.KA n∉ B.NS:= by
     intro hb
     exact disjoint_left.mp hdis hv (B.Ft _ _ hb).1
   have hret: B.MT {P.KA n}= B:= B.jH _ (by simpa using htarget)
   have hsub: A.NS ⊆A'.NS:= subset_union_left
   have hnew: A'.NS ⊆E:= by
     intro e he
     rcases mem_union.mp he with he|he
     · exact hAE he
     · rw [mem_singleton.mp he]
       exact hpair
   refine ⟨A',B,hret.symm,hsub,hnew,hBE,?_,?_,?_,?_⟩
   · simpa only [hsame] using hdis
   · rw [hsame]
   · intro e hm
     constructor
     · rintro (ha|hb)
       · rcases mem_union.mp ha with ha|ha
         · exact Or.inl ha
         · have ha':= mem_singleton.mp ha
           have hu:= congrArg Prod.fst ha'
           have hv:= congrArg Prod.snd ha'
           rw [hu,hv] at hm
           exact (hnot hm).elim
       · exact Or.inr hb
     · exact fun h=> h.imp (fun ha=> hsub ha) id
   · apply P.AY n hn A'.NS (fun i hi=> hsub (hP i hi))
     · exact mem_union_right _ (by simp)
     · exact hsub hleft
 · have hright: P.KA n∈ B.NS:=(mem_union.mp he).resolve_left hleft
   let D: G6 G M alpha beta:=
     { MG:= hM,left:= A,right:= B,NX:= P.take n (by omega),inside:= hP,
       disjoint:= hdis,distinct:= hdistinct,target:= P.KA n,
       target_mem:= hright,EV:= P.HR n hn,
       Nz:= hbridge,zV:= hnot,
       Ck:= by
         have hNo':¬Nonempty (C3 (Mv G (GQ E)) M):= by
           rw [jX]
           exact hNo
         apply pI (Fs _ _ ?_) hNo'
         intro e he
         rcases mem_union.mp he with he|he
         · apply lW
           rcases mem_union.mp he with he|he
           · exact hAE he
           · exact hBE he
         · simp only [mem_insert,mem_singleton] at he
           rcases he with rfl|rfl
           · exact lW E hpair
           · exact (xP E _ _).mpr (Or.inr hpair)}
   have hforward: D.t3.NS ⊆E:= by
     intro e he
     rcases mem_union.mp he with he|he
     · rcases mem_union.mp he with he|he
       · exact hAE he
       · rw [mem_singleton.mp he]
         exact hpair
     · exact hBE (D.xV he)
   refine ⟨D.t3,D.remaining,rfl,D.q5,hforward,
     (B.pU _).trans hBE,D.z3,D.dY,D.e3,?_⟩
   apply P.AY n hn D.t3.NS (fun i hi=> D.q5 (hP i hi))
   · exact D.t4
   · exact D.t5
end Be
end
noncomputable section
namespace Be.Bi
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {root: Fin N} (S: Bi G M root)
def Reaches (e: Fin N ×Fin N): Prop:=
 ∃P: v9 (Mv G S.NS) M root,0< P.length∧ P.KA (P.length-1)= e
lemma nD (P: v9 (Mv G S.NS) M root): P.support ⊆S.vertices:= by
 intro v hv
 obtain ⟨i,hi,rfl⟩:= mem_image.mp hv
 have hi': i≤ 2*P.length:= by have h:=mem_range.mp hi;omega
 by_cases hi0: i= 0
 · subst i
   rw [P.first]
   exact S.MU
 · have he:= P.Mu (i-1) (by omega)
   have hsub: i-1+1= i:= by omega
   rw [hsub] at he
   rcases he.2 with he|he
   · exact (S.Ft _ _ he).2
   · exact (S.Ft _ _ he).1
lemma yG (e: Fin N ×Fin N) (he: S.Reaches e): e.1∈ S.vertices∧ e.2∈ S.vertices:= by
 obtain ⟨P,hPl,hPe⟩:= he
 have ht: P.vertex (2*(P.length-1)+1)= e.1:= congrArg Prod.fst hPe
 have hh: P.vertex (2*(P.length-1)+2)= e.2:= congrArg Prod.snd hPe
 constructor
 · rw [←ht]
   exact S.nD P (P.mem_support _ (by omega))
 · rw [←hh]
   exact S.nD P (P.mem_support _ (by omega))
lemma Cv (e: Fin N ×Fin N) (he: S.Reaches e): M.Adj e.1 e.2:= by
 obtain ⟨P,hPl,hPe⟩:= he
 have hm:= P.HR (P.length-1) (by omega)
 have ht: P.vertex (2*(P.length-1)+1)= e.1:= congrArg Prod.fst hPe
 have hh: P.vertex (2*(P.length-1)+2)= e.2:= congrArg Prod.snd hPe
 rwa [ht,hh] at hm
lemma EE (e: Fin N ×Fin N) (he: e∈ S.NS) (hm: M.Adj e.1 e.2): S.Reaches e:= by
 obtain ⟨P,hPl,hPE,hPt,hPh⟩:= S.xK e.1 e.2 he hm
 let Q:= P.Kt S.NS hPE
 refine ⟨Q,hPl,?_⟩
 apply Prod.ext
 · change P.vertex (2*(P.length-1)+1)= e.1
   rw [show 2*(P.length-1)+1= 2*P.length-1 by omega]
   exact hPt
 · change P.vertex (2*(P.length-1)+2)= e.2
   rw [show 2*(P.length-1)+2= 2*P.length by omega]
   exact hPh
lemma Ij (T: Bi G M root) (hST: S.NS ⊆T.NS)
   (e: Fin N ×Fin N) (he: S.Reaches e): T.Reaches e:= by
 obtain ⟨P,hPl,hPe⟩:= he
 exact ⟨P.NM (Fs _ _ hST),hPl,hPe⟩
lemma cP {beta: Fin N} (T: Bi G M beta)
   (hd: Disjoint S.vertices T.vertices) (a b: Fin N ×Fin N)
   (ha: S.Reaches a) (hb: T.Reaches b) (hG: G.Adj a.2 b.2) (hM:¬M.Adj a.2 b.2):
   Nonempty (C3 (Mv G ((S.NS ∪T.NS) ∪{(a.2,b.2)})) M):= by
 obtain ⟨P,hPl,hPa⟩:= ha
 obtain ⟨Q,hQl,hQb⟩:= hb
 let E:=(S.NS ∪T.NS) ∪{(a.2,b.2)}
 let P':= P.NM (Fs _ _ (show S.NS ⊆E from subset_union_left.trans subset_union_left))
 let Q':= Q.NM (Fs _ _ (show T.NS ⊆E from subset_union_right.trans subset_union_left))
 have ht: P.vertex (2*P.length)= a.2:= by
   have hh: P.vertex (2*(P.length-1)+2)= a.2:= congrArg Prod.snd hPa
   rwa [show 2*(P.length-1)+2= 2*P.length by omega] at hh
 have hh: Q.vertex (2*Q.length)= b.2:= by
   have h: Q.vertex (2*(Q.length-1)+2)= b.2:= congrArg Prod.snd hQb
   rwa [show 2*(Q.length-1)+2= 2*Q.length by omega] at h
 have hbridge:(Mv G E).Adj (P'.vertex (2*P'.length)) (Q'.vertex (2*Q'.length)):= by
   change G.Adj (P.vertex (2*P.length)) (Q.vertex (2*Q.length))∧
     ((P.vertex (2*P.length),Q.vertex (2*Q.length))∈ E∨
      (Q.vertex (2*Q.length),P.vertex (2*P.length))∈ E)
   rw [ht,hh]
   exact ⟨hG,Or.inl (mem_union_right _ (mem_singleton_self _))⟩
 have hunmatched:¬M.Adj (P'.vertex (2*P'.length)) (Q'.vertex (2*Q'.length)):= by
   change ¬M.Adj (P.vertex (2*P.length)) (Q.vertex (2*Q.length))
   rwa [ht,hh]
 exact ⟨P'.Ac Q' (hd.mono (S.nD P) (T.nD Q)) hbridge hunmatched⟩
end Be.Bi
end
noncomputable section
namespace Be
variable {N: ℕ}
structure C9 (G M: SimpleGraph (Fin N)) where
 length: ℕ
 positive: 0< length
 vertex: ℕ→ Fin N
 injective:∀i j,i< 2*length→ j< 2*length→ vertex i= vertex j→ i= j
 Mu:∀i,i< 2*length-1→ G.Adj (vertex i) (vertex (i+1))
 MG:∀i,i< 2*length-1→(M.Adj (vertex i) (vertex (i+1))↔ Even i)
namespace C9
variable {G M: SimpleGraph (Fin N)} (S: C9 G M)
def support: Finset (Fin N):=(range (2*S.length)).image S.vertex
def KA (i: ℕ): Fin N ×Fin N:=(S.vertex (2*i),S.vertex (2*i+1))
lemma mem_support (i: ℕ) (hi: i< 2*S.length): S.vertex i∈ S.support:= mem_image.mpr ⟨i,mem_range.mpr hi,rfl⟩
lemma HR (i: ℕ) (hi: i< S.length): M.Adj (S.vertex (2*i)) (S.vertex (2*i+1)):= by
 exact (S.MG (2*i) (by omega)).mpr ⟨i,by omega⟩
def reverse: C9 G M where
 length:= S.length
 positive:= S.positive
 vertex i:= S.vertex (2*S.length-1-i)
 injective:= by
   intro i j hi hj he
   have hp:= S.positive
   have hh:= S.injective _ _ (by omega) (by omega) he
   omega
 Mu:= by
   intro i hi
   have hp:= S.positive
   have he: 2*S.length-1-(i+1)+1= 2*S.length-1-i:= by omega
   exact he ▸(S.Mu (2*S.length-1-(i+1)) (by omega)).symm
 MG:= by
   intro i hi
   have hp:= S.positive
   have he: 2*S.length-1-(i+1)+1= 2*S.length-1-i:= by omega
   have hh:= S.MG (2*S.length-1-(i+1)) (by omega)
   have hpar: Even (2*S.length-1-(i+1))↔ Even i:= by
     rw [Nat.even_iff,Nat.even_iff]
     omega
   rw [he] at hh
   exact (M.adj_comm _ _).trans (hh.trans hpar)
lemma CF: S.reverse.support= S.support:= by
 ext v
 have hp:= S.positive
 constructor
 · intro hv
   obtain ⟨i,hi,rfl⟩:= mem_image.mp hv
   exact S.mem_support _ (by have h:=mem_range.mp hi;change i< 2*S.length at h;omega)
 · intro hv
   obtain ⟨i,hi,rfl⟩:= mem_image.mp hv
   have hi':= mem_range.mp hi
   refine mem_image.mpr ⟨2*S.length-1-i,mem_range.mpr (by change 2*S.length-1-i< 2*S.length;omega),?_⟩
   change S.vertex (2*S.length-1-(2*S.length-1-i))= S.vertex i
   congr 1
   omega
end C9
namespace v9
variable {G M: SimpleGraph (Fin N)} {root: Fin N} (P: v9 G M root)
def segment (a b: ℕ) (hab: a≤ b) (hb: b< P.length): C9 G M where
 length:= b+1-a
 positive:= by omega
 vertex i:= P.vertex (2*a+1+i)
 injective:= by
   intro i j hi hj he
   have hh:= P.injective _ _ (by omega) (by omega) he
   omega
 Mu:= by
   intro i hi
   have h:= P.Mu (2*a+1+i) (by omega)
   simpa only [Nat.add_assoc] using h
 MG:= by
   intro i hi
   have h:= P.MG (2*a+1+i) (by omega)
   have hpar: Odd (2*a+1+i)↔ Even i:= by
     rw [Nat.odd_iff,Nat.even_iff]
     omega
   simpa only [Nat.add_assoc] using h.trans hpar
end v9
end Be
end
noncomputable section
namespace Be.v9
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {root: Fin N}
   (P: v9 G M root) (S: C9 G M)
def Iv (i: ℕ): ℕ:= i-2*P.length-1
def GF (i: ℕ): Fin N:= if i≤ 2*P.length then P.vertex i else S.vertex (P.Iv i)
lemma vW (i: ℕ) (hi0: 2*P.length< i) (hi: i≤ 2*(P.length+S.length)):
   P.Iv i< 2*S.length:= by unfold Iv;omega
lemma jK (hd: Disjoint P.support S.support) (i j: ℕ)
   (hi: i≤ 2*(P.length+S.length)) (hj: j≤ 2*(P.length+S.length))
   (heq: P.GF S i= P.GF S j): i= j:= by
 by_cases hi0: i≤ 2*P.length<;> by_cases hj0: j≤ 2*P.length
 · rw [GF,if_pos hi0,GF,if_pos hj0] at heq
   exact P.injective i j hi0 hj0 heq
 · rw [GF,if_pos hi0,GF,if_neg hj0] at heq
   exact (disjoint_left.mp hd (heq ▸P.mem_support i hi0)
     (S.mem_support _ (P.vW S j (by omega) hj))).elim
 · rw [GF,if_neg hi0,GF,if_pos hj0] at heq
   exact (disjoint_left.mp hd (heq.symm ▸P.mem_support j hj0)
     (S.mem_support _ (P.vW S i (by omega) hi))).elim
 · rw [GF,if_neg hi0,GF,if_neg hj0] at heq
   have hh:= S.injective _ _ (P.vW S i (by omega) hi) (P.vW S j (by omega) hj) heq
   unfold Iv at hh
   omega
lemma lL (hG: G.Adj (P.vertex (2*P.length)) (S.vertex 0))
   (i: ℕ) (hi: i< 2*(P.length+S.length)): G.Adj (P.GF S i) (P.GF S (i+1)):= by
 by_cases hi0: i< 2*P.length
 · rw [GF,if_pos (by omega: i≤ 2*P.length),GF,if_pos (by omega: i+1≤ 2*P.length)]
   exact P.Mu i hi0
 · by_cases hi1: i= 2*P.length
   · subst i
     rw [GF,if_pos le_rfl,GF,if_neg (by omega:¬2*P.length+1≤ 2*P.length)]
     simpa only [Iv,Nat.add_sub_cancel_left,Nat.sub_self] using hG
   · have hi2: 2*P.length< i:= by omega
     rw [GF,if_neg (by omega:¬i≤ 2*P.length),GF,if_neg (by omega:¬i+1≤ 2*P.length)]
     have hs: P.Iv (i+1)= P.Iv i+1:= by unfold Iv;omega
     rw [hs]
     exact S.Mu _ (by unfold Iv;omega)
lemma lM (hM:¬M.Adj (P.vertex (2*P.length)) (S.vertex 0))
   (i: ℕ) (hi: i< 2*(P.length+S.length)): M.Adj (P.GF S i) (P.GF S (i+1))↔ Odd i:= by
 by_cases hi0: i< 2*P.length
 · rw [GF,if_pos (by omega: i≤ 2*P.length),GF,if_pos (by omega: i+1≤ 2*P.length)]
   exact P.MG i hi0
 · by_cases hi1: i= 2*P.length
   · subst i
     rw [GF,if_pos le_rfl,GF,if_neg (by omega:¬2*P.length+1≤ 2*P.length)]
     have hz: P.Iv (2*P.length+1)= 0:= by unfold Iv;omega
     rw [hz]
     constructor
     · exact fun h=>(hM h).elim
     · rintro ⟨j,hj⟩;omega
   · have hi2: 2*P.length< i:= by omega
     rw [GF,if_neg (by omega:¬i≤ 2*P.length),GF,if_neg (by omega:¬i+1≤ 2*P.length)]
     have hs: P.Iv (i+1)= P.Iv i+1:= by unfold Iv;omega
     rw [hs]
     have hh:= S.MG (P.Iv i) (by unfold Iv;omega)
     have hp: Even (P.Iv i)↔ Odd i:= by rw [Nat.even_iff,Nat.odd_iff];unfold Iv;omega
     exact hh.trans hp
def Fr (hd: Disjoint P.support S.support)
   (hG: G.Adj (P.vertex (2*P.length)) (S.vertex 0))
   (hM:¬M.Adj (P.vertex (2*P.length)) (S.vertex 0)): v9 G M root where
 length:= P.length+S.length
 vertex:= P.GF S
 first:= by rw [GF,if_pos (by omega: 0≤ 2*P.length)];exact P.first
 injective:= P.jK S hd
 Mu:= P.lL S hG
 MG:= P.lM S hM
 L9:= P.L9
lemma l4 (hd: Disjoint P.support S.support)
   (hG: G.Adj (P.vertex (2*P.length)) (S.vertex 0))
   (hM:¬M.Adj (P.vertex (2*P.length)) (S.vertex 0)): P.M4 (P.Fr S hd hG hM):= by
 refine ⟨by change P.length≤ P.length+S.length;omega,?_⟩
 intro i hi
 exact if_pos hi
lemma wH (hd: Disjoint P.support S.support)
   (hG: G.Adj (P.vertex (2*P.length)) (S.vertex 0))
   (hM:¬M.Adj (P.vertex (2*P.length)) (S.vertex 0)) (i: ℕ):
   (P.Fr S hd hG hM).KA (P.length+i)= S.KA i:= by
 change (P.GF S (2*(P.length+i)+1),P.GF S (2*(P.length+i)+2))= _
 rw [GF,if_neg (by omega:¬2*(P.length+i)+1≤ 2*P.length),
   GF,if_neg (by omega:¬2*(P.length+i)+2≤ 2*P.length)]
 have ht: P.Iv (2*(P.length+i)+1)= 2*i:= by unfold Iv;omega
 have hh: P.Iv (2*(P.length+i)+2)= 2*i+1:= by unfold Iv;omega
 rw [ht,hh]
 rfl
end Be.v9
end
noncomputable section
namespace Be.v9
variable {N: ℕ} {G M H: SimpleGraph (Fin N)} {alpha beta: Fin N}
   (P: v9 G M alpha) (Q: v9 G M beta)
lemma GD (hM: Matching H M) (i h j: ℕ) (hi: i< P.length) (hhj: h≤ j) (hj: j< Q.length)
   (heq: P.KA i=(Q.KA j).swap)
   (hbefore:∀a,a< i→∀b,h≤ b→ b≤ j→
     s(P.vertex (2*a+1),P.vertex (2*a+2))≠ s(Q.vertex (2*b+1),Q.vertex (2*b+2))):
   ∃R: v9 G M alpha,0< R.length∧ R.KA (R.length-1)=(Q.KA h).swap:= by
 let L:= P.take i hi.le
 let T:= Q.take (j+1) (by omega)
 let S:= Q.segment h j hhj hj
 have hSep: L.Bk T (h+1):= by
   apply L.aV T hM (h+1) (by omega)
   intro a ha b hb0 hb1
   exact hbefore a ha b (by omega) (by change b< j+1 at hb1;omega)
 have hd: Disjoint L.support S.reverse.support:= by
   rw [S.CF]
   apply disjoint_left.mpr
   intro v hvL hvS
   obtain ⟨a,ha,hav⟩:= mem_image.mp hvL
   obtain ⟨b,hb,hbv⟩:= mem_image.mp hvS
   have ha': a≤ 2*i:= by have hh:=mem_range.mp ha;change a< 2*i+1 at hh;omega
   have hb': b< 2*(j+1-h):= by have hh:=mem_range.mp hb;exact hh
   have he: P.vertex a= Q.vertex (2*h+1+b):= hav.trans hbv.symm
   exact hSep a (2*h+1+b) ha' (by omega) (by change 2*h+1+b≤ 2*(j+1);omega) he
 have hfirst: S.reverse.vertex 0= Q.vertex (2*j+2):= by
   change Q.vertex (2*h+1+(2*(j+1-h)-1-0))= Q.vertex (2*j+2)
   congr 1
   omega
 have htail: P.vertex (2*i+1)= Q.vertex (2*j+2):= congrArg Prod.fst heq
 have hbridge: G.Adj (L.vertex (2*L.length)) (S.reverse.vertex 0):= by
   change G.Adj (P.vertex (2*i)) (S.reverse.vertex 0)
   rw [hfirst,←htail]
   exact P.Mu (2*i) (by omega)
 have hunmatched:¬M.Adj (L.vertex (2*L.length)) (S.reverse.vertex 0):= by
   change ¬M.Adj (P.vertex (2*i)) (S.reverse.vertex 0)
   rw [hfirst,←htail]
   exact P.zV i hi
 let R:= L.Fr S.reverse hd hbridge hunmatched
 have hlen: 0< R.length:= by change 0< i+(j+1-h);omega
 refine ⟨R,hlen,?_⟩
 have hidx: R.length-1= L.length+(S.reverse.length-1):= by
   change i+(j+1-h)-1= i+(j+1-h-1)
   omega
 change (L.Fr S.reverse hd hbridge hunmatched).KA (R.length-1)= _
 rw [hidx,L.wH S.reverse hd hbridge hunmatched]
 apply Prod.ext
 · change Q.vertex (2*h+1+(2*(j+1-h)-1-2*(j+1-h-1)))= Q.vertex (2*h+2)
   congr 1
   omega
 · change Q.vertex (2*h+1+(2*(j+1-h)-1-(2*(j+1-h-1)+1)))= Q.vertex (2*h+1)
   congr 1
   omega
end Be.v9
end
noncomputable section
namespace Be
variable {N: ℕ}
def Fk (G M: SimpleGraph (Fin N)) (root: Fin N) (a: Fin N ×Fin N): Prop:=
 ∃P: v9 G M root,0< P.length∧ P.KA (P.length-1)= a
def G2 (G M: SimpleGraph (Fin N)) (root: Fin N) (a b: Fin N ×Fin N): Prop:=
 ∀P: v9 G M root,0< P.length→ P.KA (P.length-1)= b→¬P.Nt {a}
namespace v9
variable {G M: SimpleGraph (Fin N)} {root: Fin N} (P: v9 G M root)
lemma KW (i: ℕ) (hi: i< P.length): Fk G M root (P.KA i):= by
 refine ⟨P.take (i+1) (by omega),by change 0< i+1;omega,?_⟩
 change P.KA (i+1-1)= P.KA i
 rw [Nat.add_sub_cancel]
end v9
lemma Dz {G M: SimpleGraph (Fin N)} {root: Fin N} (a: Fin N ×Fin N): G2 G M root a a:= by
 intro P hPl hP hA
 have h:= hA (P.length-1) (by omega)
 exact h (mem_singleton.mpr hP)
lemma wV {G M H: SimpleGraph (Fin N)} {root: Fin N}
   (hM: Matching H M) (a b: Fin N ×Fin N) (hNo:¬Fk G M root a.swap)
   (hb: Fk G M root b) (hDom: G2 G M root a b): G2 G M root a b.swap:= by
 obtain ⟨Q,hQl,hQlast⟩:= hb
 have hQnot:= hDom Q hQl hQlast
 have hcontains:∃h,h< Q.length∧ Q.KA h= a:= by
   by_contra hex
   apply hQnot
   intro i hi hmem
   exact hex ⟨i,hi,mem_singleton.mp hmem⟩
 obtain ⟨h,hh,hQa⟩:= hcontains
 intro P hPl hPlast hPA
 let C:=(range P.length).filter (fun k=>∃j,h≤ j∧ j< Q.length∧
   s(P.vertex (2*k+1),P.vertex (2*k+2))= s(Q.vertex (2*j+1),Q.vertex (2*j+2)))
 have hC: C.Nonempty:= by
   refine ⟨P.length-1,mem_filter.mpr ⟨mem_range.mpr (by omega),Q.length-1,by omega,by omega,?_⟩⟩
   have hp: P.KA (P.length-1)=(Q.KA (Q.length-1)).swap:=
     hPlast.trans (congrArg Prod.swap hQlast).symm
   have hs:= congrArg (fun p=> s(p.1,p.2)) hp
   exact hs.trans Sym2.eq_swap
 let k:= C.min' hC
 have hkC: k∈ C:= min'_mem C hC
 have hk: k< P.length:= mem_range.mp (mem_filter.mp hkC).1
 obtain ⟨j,hjh,hj,heq⟩:=(mem_filter.mp hkC).2
 have hbefore:∀i,i< k→∀t,h≤ t→ t< Q.length→
     s(P.vertex (2*i+1),P.vertex (2*i+2))≠ s(Q.vertex (2*t+1),Q.vertex (2*t+2)):= by
   intro i hi t hth ht het
   have hiC: i∈ C:= mem_filter.mpr ⟨mem_range.mpr (by omega),t,hth,ht,het⟩
   have hki:= min'_le C i hiC
   omega
 rcases Sym2.eq_iff.mp heq with hsame|hreverse
 · have hpairs: P.KA k= Q.KA j:= Prod.ext hsame.1 hsame.2
   have hjh': h< j:= by
     by_contra hle
     have hje: j= h:= by omega
     have hbad:= hPA k hk
     exact hbad (mem_singleton.mpr (hpairs.trans ((congrArg Q.KA hje).trans hQa)))
   have htail:∀t,j≤ t→ t< Q.length→ Q.KA t∉({a}: Finset _):= by
     intro t hjt ht hmem
     have hth:= Q.pB t h ht hh ((mem_singleton.mp hmem).trans hQa.symm)
     omega
   obtain ⟨R,hRl,hRE,hRA,hRlast⟩:= P.FR Q hM k j hk hj hpairs
     (fun i hi t hjt ht=> hbefore i hi t (by omega) ht) univ {a}
     (by intro i hi;simp) (by intro i hi;simp) hPA htail
   exact hDom R hRl (hRlast.trans hQlast) hRA
 · have hpairs: P.KA k=(Q.KA j).swap:= Prod.ext hreverse.1 hreverse.2
   obtain ⟨R,hRl,hRlast⟩:= P.GD Q hM k h j hk hjh hj hpairs
     (fun i hi t hth htj=> hbefore i hi t hth (by omega))
   apply hNo
   exact ⟨R,hRl,hRlast.trans (congrArg Prod.swap hQa)⟩
end Be
end
noncomputable section
namespace Be.Bi
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {root: Fin N} (S: Bi G M root)
def qK: Prop:=∀P: v9 (Mv G S.NS) M root,P.Nv S.NS
lemma Ii (e: Fin N ×Fin N) (he: S.Reaches e): e∈ S.NS∨ e.swap∈ S.NS:= by
 obtain ⟨P,hPl,hPe⟩:= he
 have ht: P.vertex (2*(P.length-1)+1)= e.1:= congrArg Prod.fst hPe
 have hh: P.vertex (2*(P.length-1)+2)= e.2:= congrArg Prod.snd hPe
 have hg:=(P.Mu (2*(P.length-1)+1) (by omega)).2
 change (P.vertex (2*(P.length-1)+1),P.vertex (2*(P.length-1)+2))∈ S.NS∨
   (P.vertex (2*(P.length-1)+2),P.vertex (2*(P.length-1)+1))∈ S.NS at hg
 rwa [ht,hh] at hg
def KK: Finset (Fin N ×Fin N):= univ.filter (fun e=>
 (¬M.Adj e.1 e.2∧(e∈ S.NS∨ e.swap∈ S.NS))∨ S.Reaches e)
lemma Cl: S.NS ⊆S.KK:= by
 intro e he
 apply mem_filter.mpr
 refine ⟨mem_univ _,?_⟩
 by_cases hm: M.Adj e.1 e.2
 · exact Or.inr (S.EE e he hm)
 · exact Or.inl ⟨hm,Or.inl he⟩
lemma Gk (e: Fin N ×Fin N) (he: e∈ S.KK): e∈ S.NS∨ e.swap∈ S.NS:= by
 rcases (mem_filter.mp he).2 with he|he
 · exact he.2
 · exact S.Ii e he
lemma H8 (u v: Fin N) (he:(u,v)∈ S.KK): G.Adj u v:= by
 rcases S.Gk (u,v) he with he|he
 · exact S.valid u v he
 · exact (S.valid v u he).symm
lemma Ay (u v: Fin N) (he:(u,v)∈ S.KK): u∈ S.vertices∧ v∈ S.vertices:= by
 rcases S.Gk (u,v) he with he|he
 · exact S.Ft u v he
 · exact (S.Ft v u he).symm
lemma c5 (P: v9 (Mv G S.NS) M root): P.Nv S.KK:= by
 intro i hi
 apply mem_filter.mpr
 refine ⟨mem_univ _,?_⟩
 by_cases hm: M.Adj (P.vertex i) (P.vertex (i+1))
 · obtain ⟨j,hj⟩:=(P.MG i hi).mp hm
   have hij: i= 2*j+1:= by omega
   right
   have hr:= P.KW j (by omega)
   change S.Reaches (P.KA j) at hr
   rw [hij]
   exact hr
 · exact Or.inl ⟨hm,(P.Mu i hi).2⟩
def normalized: Bi G M root where
 NS:= S.KK
 L9:= S.L9
 valid:= S.H8
 xK:= by
   intro u v he hm
   have hr: S.Reaches (u,v):= by
     rcases (mem_filter.mp he).2 with he|he
     · exact (he.1 hm).elim
     · exact he
   obtain ⟨P,hPl,hLast⟩:= hr
   let Q:= P.NM (show Mv G S.NS≤ G from fun _ _ h=> h.1)
   have hQ: Q.Nv S.KK:= S.c5 P
   have ht: P.vertex (2*(P.length-1)+1)= u:= congrArg Prod.fst hLast
   have hh: P.vertex (2*(P.length-1)+2)= v:= congrArg Prod.snd hLast
   rw [show 2*(P.length-1)+1= 2*P.length-1 by omega] at ht
   rw [show 2*(P.length-1)+2= 2*P.length by omega] at hh
   exact ⟨Q,hPl,hQ,ht,hh⟩
 LD:= by
   intro u v he
   have huv:= S.Ay u v he
   exact ⟨(S.wS u huv.1).imp id (Hn S.Cl),
     (S.wS v huv.2).imp id (Hn S.Cl)⟩
lemma Az: Mv G S.normalized.NS= Mv G S.NS:= by
 ext u v
 constructor
 · rintro ⟨hG,he|he⟩
   · exact ⟨hG,S.Gk (u,v) he⟩
   · exact ⟨hG,(S.Gk (v,u) he).symm⟩
 · rintro ⟨hG,he|he⟩
   · exact ⟨hG,Or.inl (S.Cl he)⟩
   · exact ⟨hG,Or.inr (S.Cl he)⟩
lemma r8: S.normalized.vertices= S.vertices:= by
 apply Subset.antisymm
 · intro v hv
   rcases mem_union.mp hv with hv|hv
   · exact mem_union_left _ hv
   · obtain ⟨e,he,hv⟩:= mem_biUnion.mp hv
     have hh:= S.Ay e.1 e.2 he
     rcases mem_insert.mp hv with hv|hv
     · exact hv.symm ▸hh.1
     · exact (mem_singleton.mp hv).symm ▸hh.2
 · intro v hv
   rcases mem_union.mp hv with hv|hv
   · exact mem_union_left _ hv
   · obtain ⟨e,he,hv⟩:= mem_biUnion.mp hv
     exact mem_union_right _ (mem_biUnion.mpr ⟨e,S.Cl he,hv⟩)
lemma r6: S.normalized.qK:= by
 intro P
 let Q:= P.NM (le_of_eq S.Az)
 exact S.c5 Q
end Be.Bi
end
noncomputable section
namespace Be.Bi
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {root: Fin N} (S: Bi G M root)
lemma u0 (a: Fin N ×Fin N): S.normalized.Reaches a↔ S.Reaches a:= by
 constructor
 · rintro ⟨P,hPl,hLast⟩
   exact ⟨P.NM (le_of_eq S.Az),hPl,hLast⟩
 · rintro ⟨P,hPl,hLast⟩
   exact ⟨P.NM (le_of_eq S.Az.symm),hPl,hLast⟩
lemma mJ (hS: S.qK) (a: Fin N ×Fin N) (ha: S.Reaches a): a∈ S.NS:= by
 obtain ⟨P,hPl,hLast⟩:= ha
 have hIn:= hS P (2*(P.length-1)+1) (by omega)
 change (P.vertex (2*(P.length-1)+1),P.vertex (2*(P.length-1)+2))∈ S.NS at hIn
 change (P.vertex (2*(P.length-1)+1),P.vertex (2*(P.length-1)+2))= a at hLast
 rwa [hLast] at hIn
lemma mI (hS: S.qK) (F: Finset (Fin N ×Fin N)) (a: Fin N ×Fin N):
   lZ G M root S.NS F a↔
     ∃P: v9 (Mv G S.NS) M root,
       0< P.length∧ P.Nt F∧ P.KA (P.length-1)= a:= by
 constructor
 · rintro ⟨P,hPl,hP,hF,hLast⟩
   exact ⟨P.Kt S.NS hP,hPl,hF,hLast⟩
 · rintro ⟨P,hPl,hF,hLast⟩
   let Q:= P.NM (show Mv G S.NS≤ G from fun _ _ h=> h.1)
   exact ⟨Q,hPl,hS P,hF,hLast⟩
lemma b9 (hS: S.qK) (F: Finset (Fin N ×Fin N))
   (a: Fin N ×Fin N):
   a∈ S.CD F↔
     ∃P: v9 (Mv G S.NS) M root,
       0< P.length∧ P.Nt F∧ P.KA (P.length-1)= a:= by
 constructor
 · intro ha
   obtain ⟨he,hm,P,hPl,hP,hF,hLast⟩:= mem_filter.mp ha
   exact (S.mI hS F a).mp ⟨P,hPl,hP,hF,hLast⟩
 · intro ha
   have hreach: S.Reaches a:= by obtain ⟨P,hPl,hF,hLast⟩:= ha;exact ⟨P,hPl,hLast⟩
   have he:= S.mJ hS a hreach
   have hm:= S.Cv a hreach
   obtain ⟨P,hPl,hP,hF,hLast⟩:=(S.mI hS F a).mpr ha
   exact mem_filter.mpr ⟨he,hm,P,hPl,hP,hF,hLast⟩
end Be.Bi
end
noncomputable section
namespace Be.Bi
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {root: Fin N} (S: Bi G M root)
lemma yK (hS: S.qK) (F: Finset (Fin N ×Fin N))
   (hF:∀a∈ F,a.1∉(S.MT F).vertices):(S.MT F).qK:= by
 intro P
 let Q:= P.NM (Fs _ _ (S.pU F))
 let R:= P.NM (show Mv G (S.MT F).NS≤ G from fun _ _ h=> h.1)
 have hInside: R.Nv S.NS:= hS Q
 have hAvoid: R.Nt F:= by
   intro i hi hmem
   change i< P.length at hi
   have hv:=(S.MT F).nD P (P.mem_support (2*i+1) (by omega))
   exact hF (R.KA i) hmem hv
 exact S.jY F R hInside hAvoid
end Be.Bi
namespace Be.G6
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {alpha beta: Fin N} (D: G6 G M alpha beta)
end Be.G6
end
noncomputable section
namespace Be
variable {N: ℕ} {G M H: SimpleGraph (Fin N)} {alpha beta: Fin N}
namespace Bi
variable {root: Fin N} (S: Bi G M root)
lemma pW (hM: Matching H M) (hS: S.qK)
   (target e: Fin N ×Fin N) (hNo:¬S.Reaches target.swap)
   (he: S.Reaches e) (hrev: S.Reaches e.swap):
   e∈ S.CD {target}↔ e.swap∈ S.CD {target}:= by
 have hprop (a: Fin N ×Fin N) (ha: S.Reaches a) (haRev: S.Reaches a.swap)
     (hnot: a∉ S.CD {target}): a.swap∉ S.CD {target}:= by
   have hDom: G2 (Mv G S.NS) M root target a:= by
     intro P hPl hLast hAvoid
     exact hnot ((S.b9 hS {target} a).mpr ⟨P,hPl,hAvoid,hLast⟩)
   have hDomRev:= wV hM target a hNo ha hDom
   intro hr
   obtain ⟨P,hPl,hAvoid,hLast⟩:=(S.b9 hS {target} a.swap).mp hr
   exact hDomRev P hPl hLast hAvoid
 constructor
 · intro hr
   by_contra hnot
   have hh:= hprop e.swap hrev (by simpa only [Prod.swap_swap] using he) hnot
   exact hh (by simpa only [Prod.swap_swap] using hr)
 · intro hr
   by_contra hnot
   exact hprop e he hrev hnot hr
end Bi
lemma a1 (A: Bi G M alpha) (B: Bi G M beta)
   (P: v9 G M alpha) (n: ℕ) (hn: n< P.length)
   (E: Finset (Fin N ×Fin N)) (hAE: A.NS ⊆E) (hBE: B.NS ⊆E) (hPE: P.Nv E)
   (hNo:¬Nonempty (C3 (Mv G E) M))
   (hdis: Disjoint A.vertices B.vertices) (hP:(P.take n (by omega)).Nv A.NS):
   ¬B.Reaches (P.KA n).swap:= by
 rintro ⟨Q,hQl,hLast⟩
 let L:=(P.take n (by omega)).Kt E (fun i hi=> hAE (hP i hi))
 let R:= Q.NM (Fs _ _ hBE)
 have hd: Disjoint L.support R.support:= hdis.mono
   (A.EA (P.take n (by omega)) hP) (B.nD Q)
 have hhead: Q.vertex (2*Q.length)= P.vertex (2*n+1):= by
   have hh: Q.vertex (2*(Q.length-1)+2)= P.vertex (2*n+1):= congrArg Prod.snd hLast
   rwa [show 2*(Q.length-1)+2= 2*Q.length by omega] at hh
 have hg:(Mv G E).Adj (L.vertex (2*L.length)) (R.vertex (2*R.length)):= by
   change G.Adj (P.vertex (2*n)) (Q.vertex (2*Q.length))∧
     ((P.vertex (2*n),Q.vertex (2*Q.length))∈ E∨(Q.vertex (2*Q.length),P.vertex (2*n))∈ E)
   rw [hhead]
   exact ⟨P.Mu (2*n) (by omega),Or.inl (hPE (2*n) (by omega))⟩
 have hm:¬M.Adj (L.vertex (2*L.length)) (R.vertex (2*R.length)):= by
   change ¬M.Adj (P.vertex (2*n)) (Q.vertex (2*Q.length))
   rw [hhead]
   exact P.zV n hn
 exact hNo ⟨L.Ac R hd hg hm⟩
lemma eJ (hM: Matching H M) (A: Bi G M alpha) (B: Bi G M beta)
   (A': Bi G M alpha) (B': Bi G M beta) (target: Fin N ×Fin N)
   (hB: B.qK) (hNo:¬B.Reaches target.swap)
   (hret: B'= B.MT {target})
   (hpart:∀e,M.Adj e.1 e.2→(e∈ A'.NS∨ e∈ B'.NS↔ e∈ A.NS∨ e∈ B.NS))
   (e: Fin N ×Fin N) (he: B.Reaches e) (hrev: B.Reaches e.swap):
   (A'.Reaches e∧ A'.Reaches e.swap)∨(B'.Reaches e∧ B'.Reaches e.swap):= by
 have heM:= B.Cv e he
 have hrM:= B.Cv e.swap hrev
 have hiff:= B.pW hM hB target e hNo he hrev
 by_cases hkeep: e∈ B.CD {target}
 · have hmem: e∈ B'.NS:= by rw [hret];exact mem_union_left _ hkeep
   have hmemRev: e.swap∈ B'.NS:= by rw [hret];exact mem_union_left _ (hiff.mp hkeep)
   exact Or.inr ⟨B'.EE e hmem heM,B'.EE e.swap hmemRev hrM⟩
 · have hnotRev: e.swap∉ B.CD {target}:= fun h=> hkeep (hiff.mpr h)
   have hleft (a: Fin N ×Fin N) (ha: B.Reaches a) (hnot: a∉ B.CD {target}): A'.Reaches a:= by
     have hm:= B.Cv a ha
     have hmem:= B.mJ hB a ha
     rcases (hpart a hm).mpr (Or.inr hmem) with hl|hr
     · exact A'.EE a hl hm
     · rw [hret] at hr
       exact (hnot ((B.pV {target} a.1 a.2 hm).mp hr)).elim
   exact Or.inl ⟨hleft e he hkeep,hleft e.swap hrev hnotRev⟩
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {alpha beta: Fin N}
namespace v9
variable {root: Fin N} (P: v9 G M root)
def L5 (k n: ℕ): Finset (Fin N ×Fin N):=(Ico k n).image P.KA
lemma EB (k: ℕ): P.L5 k k=∅:= by simp [L5]
lemma EC (k n: ℕ) (hkn: k≤ n):
   P.L5 k (n+1)= P.L5 k n ∪{P.KA n}:= by
 simp only [L5,Nat.Ico_succ_right_eq_insert_Ico hkn,image_insert]
 ext a
 simp only [mem_insert,mem_union,mem_singleton]
 tauto
end v9
structure IQ (A: Bi G M alpha) (B: Bi G M beta)
   (P: v9 G M alpha) (k n: ℕ) (hn: n≤ P.length) (E: Finset (Fin N ×Fin N)) where
 left: Bi G M alpha
 right: Bi G M beta
 MT: right= B.MT (P.L5 k n)
 NL: A.NS ⊆left.NS
 Jl: left.NS ⊆E
 Is: right.NS ⊆E
 disjoint: Disjoint left.vertices right.vertices
 vertices: left.vertices ∪right.vertices= A.vertices ∪B.vertices
 matched:∀e,M.Adj e.1 e.2→(e∈ left.NS∨ e∈ right.NS↔ e∈ A.NS∨ e∈ B.NS)
 active:(P.take n hn).Nv left.NS
 No: B.qK→∀e,B.Reaches e→ B.Reaches e.swap→
   (left.Reaches e∧ left.Reaches e.swap)∨(right.Reaches e∧ right.Reaches e.swap)
namespace IQ
variable {A: Bi G M alpha} {B: Bi G M beta}
   {P: v9 G M alpha} {k n: ℕ} {hn: n≤ P.length}
   {E: Finset (Fin N ×Fin N)} (S: IQ A B P k n hn E)
lemma EP (hB: B.qK): S.right.qK:= by
 have hF:∀a∈ P.L5 k n,a.1∉ S.right.vertices:= by
   intro a ha hv
   obtain ⟨i,hi,hia⟩:= mem_image.mp ha
   have hi':=(mem_Ico.mp hi).2
   have he: P.KA i∈ S.left.NS:= S.active (2*i+1) (by change 2*i+1< 2*n;omega)
   have haL: a∈ S.left.NS:= hia ▸he
   exact disjoint_left.mp S.disjoint (S.left.Ft a.1 a.2 haL).1 hv
 rw [S.MT] at hF ⊢
 exact B.yK hB _ hF
end IQ
lemma GO (hM: Matching G M) (A: Bi G M alpha) (B: Bi G M beta)
   (P: v9 G M alpha) (k: ℕ) (hk: k≤ P.length)
   (E: Finset (Fin N ×Fin N))
   (hAE: A.NS ⊆E) (hBE: B.NS ⊆E) (hPE: P.Nv E)
   (hNo:¬Nonempty (C3 (Mv G E) M))
   (hdis: Disjoint A.vertices B.vertices)
   (hP:(P.take k hk).Nv A.NS)
   (he:∀n,k≤ n→ n< P.length→ P.KA n∈ A.NS ∪B.NS)
   (t: ℕ) (ht: k+t≤ P.length): Nonempty (IQ A B P k (k+t) ht E):= by
 induction t with
 | zero =>
   refine ⟨{
     left:= A
     right:= B
     MT:= ?_
     NL:= subset_refl _
     Jl:= hAE
     Is:= hBE
     disjoint:= hdis
     vertices:= rfl
     matched:= fun _ _=> Iff.rfl
     No:= fun _ _ he hrev=> Or.inr ⟨he,hrev⟩
     active:= hP}⟩
   rw [Nat.add_zero,P.EB]
   exact (B.jH ∅ (by simp)).symm
 | succ t ih =>
   have ht': k+t≤ P.length:= by omega
   obtain ⟨S⟩:= ih ht'
   have hnext: k+t< P.length:= by omega
   have htarget: P.KA (k+t)∈ S.left.NS ∪S.right.NS:= by
     apply mem_union.mpr
     exact (S.matched _ (P.HR _ hnext)).mpr (mem_union.mp (he _ (by omega) hnext))
   obtain ⟨A',B',hret,hgrows,hleft,hright,hdis',hvertices,hmatched,hactive⟩:=
     sZ hM S.left S.right P (k+t) hnext E S.Jl S.Is hPE hNo S.disjoint S.active htarget
   have hret': B'= B.MT (P.L5 k (k+(t+1))):= by
     rw [hret,S.MT,B.EO]
     congr 1
     simpa only [Nat.add_assoc] using (P.EC k (k+t) (by omega)).symm
   refine ⟨{
     left:= A'
     right:= B'
     MT:= hret'
     NL:= S.NL.trans hgrows
     Jl:= hleft
     Is:= hright
     disjoint:= hdis'
     vertices:= hvertices.trans S.vertices
     matched:= fun e hm=>(hmatched e hm).trans (S.matched e hm)
     No:= by
       intro hBcomp e he hrev
       rcases S.No hBcomp e he hrev with hsettled|hsettled
       · exact Or.inl ⟨S.left.Ij A' hgrows e hsettled.1,S.left.Ij A' hgrows e.swap hsettled.2⟩
       · exact eJ hM S.left S.right A' B' (P.KA (k+t)) (S.EP hBcomp)
           (a1 S.left S.right P (k+t) hnext E S.Jl S.Is hPE hNo S.disjoint S.active)
           hret hmatched e hsettled.1 hsettled.2
     active:= ?_}⟩
   exact hactive
lemma CQ (hM: Matching G M) (A: Bi G M alpha) (B: Bi G M beta)
   (P: v9 G M alpha) (k: ℕ) (hk: k≤ P.length)
   (E: Finset (Fin N ×Fin N))
   (hAE: A.NS ⊆E) (hBE: B.NS ⊆E) (hPE: P.Nv E)
   (hNo:¬Nonempty (C3 (Mv G E) M))
   (hdis: Disjoint A.vertices B.vertices)
   (hP:(P.take k hk).Nv A.NS)
   (he:∀n,k≤ n→ n< P.length→ P.KA n∈ A.NS ∪B.NS):
   Nonempty (IQ A B P k P.length le_rfl E):= by
 have h:= GO hM A B P k hk E hAE hBE hPE hNo hdis hP he (P.length-k) (by omega)
 simpa only [Nat.add_sub_of_le hk] using h
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {root: Fin N}
namespace v9
variable (P: v9 G M root)
def La (j: ℕ): Finset (Fin N ×Fin N):=
 ((range P.length).filter (fun i=> j≤ i+1)).image P.KA
lemma oI (j: ℕ) (hj1: 1≤ j) (hj: j≤ P.length+1):
   (P.take (j-1) (by omega)).Nt (P.La j):= by
 intro i hi hmem
 change i< j-1 at hi
 obtain ⟨k,hk,heq⟩:= mem_image.mp hmem
 have hkl: k< P.length:= mem_range.mp (mem_filter.mp hk).1
 have hkj:=(mem_filter.mp hk).2
 have hki: k= i:= P.pB k i hkl (by omega) heq
 omega
end v9
namespace Bi
variable (S: Bi G M root) (P: v9 G M root) (hP: P.Nv S.NS)
include hP in
lemma lB (j: ℕ) (hj1: 1≤ j) (hj: j≤ P.length+1):
   (P.take (j-1) (by omega)).Nv (S.Ip (P.La j)):= by
 exact S.jY (P.La j) _ (P.JJ S.NS hP (j-1) (by omega)) (P.oI j hj1 hj)
include hP in
lemma lC (a: Fin N ×Fin N) (ha:∀i,i< P.length→ P.KA i≠ a):
   P.Nv (S.Ip {a}):= by
 apply S.jY {a} P hP
 intro i hi hmem
 exact ha i hi (mem_singleton.mp hmem)
end Bi
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {alpha beta: Fin N}
structure C2 (G M: SimpleGraph (Fin N)) (alpha beta: Fin N) where
 data: G6 G M alpha beta
 Ng: v9 G M beta
 inside: Ng.Nv data.right.NS
 index: ℕ
 positive: 1≤ index
 bound: index≤ Ng.length
 target: Ng.KA (index-1)= data.target
namespace C2
variable (D: C2 G M alpha beta)
lemma separation: D.data.NX.Bk D.Ng D.index:=
 D.data.NX.dH D.Ng D.index
   (D.data.disjoint.mono (D.data.left.EA D.data.NX D.data.inside)
     (D.data.right.EA D.Ng D.inside))
lemma JK: D.Ng.vertex (2*D.index-1)= D.data.target.1:= by
 have h:= congrArg Prod.fst D.target
 change D.Ng.vertex (2*(D.index-1)+1)= D.data.target.1 at h
 rw [show 2*(D.index-1)+1= 2*D.index-1 by have hp:=D.positive;omega] at h
 exact h
lemma Nz: G.Adj (D.data.NX.vertex (2*D.data.NX.length)) (D.Ng.vertex (2*D.index-1)):= by
 rw [D.JK]
 exact D.data.Nz
lemma zV:¬M.Adj (D.data.NX.vertex (2*D.data.NX.length)) (D.Ng.vertex (2*D.index-1)):= by
 rw [D.JK]
 exact D.data.zV
def path: v9 G M alpha:=
 D.data.NX.CO D.Ng D.index D.positive D.bound D.separation D.Nz D.zV
def NG: Finset (Fin N ×Fin N):= D.data.KC
lemma vB: D.path.Nv D.NG:= by
 apply D.data.NX.lT D.Ng D.index D.positive D.bound D.separation D.Nz D.zV
 · intro i hi
   exact D.data.BX (D.data.inside i hi)
 · intro i _ hi
   exact D.data.AO (D.inside i hi)
 · rw [D.JK]
   exact mem_union_right _ (by simp)
lemma Id:(D.path.take D.data.NX.length (by change D.data.NX.length≤ D.data.NX.length+(D.Ng.length+1-D.index);omega)).Nv D.data.left.NS:= by
 intro i hi
 change i< 2*D.data.NX.length at hi
 change (D.data.NX.Iy D.Ng D.index i,D.data.NX.Iy D.Ng D.index (i+1))∈ D.data.left.NS
 rw [v9.Iy,if_pos (by omega: i≤ 2*D.data.NX.length),
   v9.Iy,if_pos (by omega: i+1≤ 2*D.data.NX.length)]
 exact D.data.inside i hi
lemma IA (i: ℕ) (hi: D.data.NX.length≤ i) (hi': i< D.path.length):
   D.path.KA i∈ D.data.left.NS ∪D.data.right.NS:= by
 have hlen: i< D.data.NX.length+(D.Ng.length+1-D.index):= hi'
 have hp:= D.positive
 have hb:= D.bound
 have ha:= D.data.NX.fQ D.Ng D.index D.positive D.bound D.separation D.Nz D.zV i hi
 change D.path.KA i= _ at ha
 rw [ha]
 exact mem_union_right _ (D.inside (2*(i-D.data.NX.length+D.index-1)+1) (by omega))
lemma sI: D.path.L5 D.data.NX.length D.path.length= D.Ng.La D.index:= by
 ext e
 constructor
 · intro he
   obtain ⟨i,hi,rfl⟩:= mem_image.mp he
   have hi0:=(mem_Ico.mp hi).1
   have hi1:=(mem_Ico.mp hi).2
   have hlen: i< D.data.NX.length+(D.Ng.length+1-D.index):= hi1
   have hp:= D.positive
   have hb:= D.bound
   have ha:= D.data.NX.fQ D.Ng D.index D.positive D.bound D.separation D.Nz D.zV i hi0
   change D.path.KA i= _ at ha
   rw [ha]
   exact mem_image.mpr ⟨i-D.data.NX.length+D.index-1,mem_filter.mpr ⟨mem_range.mpr (by omega),by omega⟩,rfl⟩
 · intro he
   obtain ⟨i,hi,rfl⟩:= mem_image.mp he
   obtain ⟨hi1,hi0⟩:= mem_filter.mp hi
   have hi1':= mem_range.mp hi1
   have hp:= D.positive
   have hb:= D.bound
   let n:= D.data.NX.length+(i+1-D.index)
   have hn0: D.data.NX.length≤ n:= by dsimp [n];omega
   have hn1: n< D.path.length:= by change n< D.data.NX.length+(D.Ng.length+1-D.index);dsimp [n];omega
   refine mem_image.mpr ⟨n,mem_Ico.mpr ⟨hn0,hn1⟩,?_⟩
   have ha:= D.data.NX.fQ D.Ng D.index D.positive D.bound D.separation D.Nz D.zV n hn0
   change D.path.KA n= _ at ha
   rw [ha]
   congr 1
   dsimp [n]
   omega
lemma transfer: Nonempty (IQ D.data.left D.data.right D.path D.data.NX.length D.path.length le_rfl D.NG):= by
 apply CQ D.data.MG D.data.left D.data.right D.path D.data.NX.length
   (by change D.data.NX.length≤ D.data.NX.length+(D.Ng.length+1-D.index);omega)
   D.NG D.data.BX D.data.AO D.vB
 · exact D.data.Ck
 · exact D.data.disjoint
 · exact D.Id
 · exact D.IA
lemma labels (ell: ℕ) (lab: Fin N ×Fin N→ ℕ) (hQ: D.Ng.Mq ell lab)
   (hlabel: D.data.NX.length+1< lab D.data.target):
   D.path.Mq ell (D.path.Nl lab)∧ D.path.Nl lab D.data.target< lab D.data.target:= by
 have h:= D.data.NX.h4 D.Ng D.index D.positive D.bound D.separation D.Nz D.zV ell lab hQ
   (by rw [D.target];exact hlabel)
 change D.path.Mq ell (D.path.Nl lab)∧ D.path.Nl lab (D.Ng.KA (D.index-1))< lab (D.Ng.KA (D.index-1)) at h
 simpa only [D.target] using h
end C2
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {alpha beta: Fin N}
lemma Bi.Gi (A: Bi G M alpha) (B: Bi G M beta)
   (hd: Disjoint A.vertices B.vertices) (e: Fin N ×Fin N) (he: e∈ A.NS): e∉ B.NS:= by
 intro hb
 exact disjoint_left.mp hd (A.Ft e.1 e.2 he).1 (B.Ft e.1 e.2 hb).1
namespace IQ
variable {A: Bi G M alpha} {B: Bi G M beta}
   {P: v9 G M alpha} {k n: ℕ} {hn: n≤ P.length}
   {E: Finset (Fin N ×Fin N)} (S: IQ A B P k n hn E)
lemma Af (e: Fin N ×Fin N) (hm: M.Adj e.1 e.2):
   e∈ S.left.NS↔ e∈ A.NS∨(e∈ B.NS∧ e∉ B.Ip (P.L5 k n)):= by
 have hnot (he: e∈ S.left.NS): e∉ S.right.NS:= S.left.Gi S.right S.disjoint e he
 constructor
 · intro he
   rcases (S.matched e hm).mp (Or.inl he) with ha|hb
   · exact Or.inl ha
   · refine Or.inr ⟨hb,?_⟩
     intro hr
     apply hnot he
     rw [S.MT]
     exact hr
 · rintro (ha|⟨hb,hr⟩)
   · exact S.NL ha
   · rcases (S.matched e hm).mpr (Or.inr hb) with hl|hr'
     · exact hl
     · rw [S.MT] at hr'
       exact (hr hr').elim
end IQ
namespace C2
variable (D: C2 G M alpha beta)
lemma pM:
   ∃(A: Bi G M alpha) (B: Bi G M beta),
     B= D.data.right.MT (D.Ng.La D.index)∧
     D.data.left.NS ⊆A.NS∧ A.NS ⊆D.data.KC∧
     Disjoint A.vertices B.vertices∧ A.vertices ∪B.vertices= D.data.left.vertices ∪D.data.right.vertices∧
     D.path.Nv A.NS∧
     (D.Ng.take (D.index-1) (by have hb:=D.bound;omega)).Nv B.NS∧
     (∀e,M.Adj e.1 e.2→(e∈ A.NS↔ e∈ D.data.left.NS∨
       (e∈ D.data.right.NS∧ e∉ D.data.right.Ip (D.Ng.La D.index)))):= by
 obtain ⟨S⟩:= D.transfer
 have hr: S.right= D.data.right.MT (D.Ng.La D.index):= by
   rw [S.MT,D.sI]
 refine ⟨S.left,S.right,hr,S.NL,S.Jl,S.disjoint,S.vertices,S.active,?_,?_⟩
 · rw [hr]
   exact D.data.right.lB D.Ng D.inside D.index D.positive (by have hb:=D.bound;omega)
 · intro e hm
   have h:= S.Af e hm
   rw [D.sI] at h
   exact h
lemma CE (ell: ℕ) (lab: Fin N ×Fin N→ ℕ) (hQ: D.Ng.Mq ell lab):
   (D.Ng.take (D.index-1) (by have hb:=D.bound;omega)).Mq ell (D.path.Nl lab):= by
 apply (D.Ng.take (D.index-1) (by have hb:=D.bound;omega)).F5 ell lab (D.path.Nl lab)
 · exact D.Ng.GR ell lab hQ (D.index-1) (by have hb:=D.bound;omega)
 · exact D.path.Ik lab
end C2
end Be
end
noncomputable section
namespace Be
variable {N: ℕ}
structure Lp (G M: SimpleGraph (Fin N)) (root: Fin N) where
 tree: Bi G M root
 active: Option (v9 G M root)
 inside:∀P,active= some P→ P.Nv tree.NS
 NU: Bool
 modified: Bool
 extended: Bool
namespace Lp
variable {G M: SimpleGraph (Fin N)} {root: Fin N} (S: Lp G M root)
def Mq (ell: ℕ) (labels: Fin N ×Fin N→ ℕ): Prop:=
 ∀P,S.active= some P→ P.Mq ell labels
def Dg: Finset (Fin N):= S.active.elim ∅ v9.support
def IX (limit: ℕ): Lp G M root:=
 { S with NU:= S.NU&& decide (limit≤ S.tree.vertices.card),modified:= false,extended:= false}
def rC (limit: ℕ): Lp G M root:=
 { S with NU:= S.NU|| decide (limit≤ S.tree.vertices.card)}
def backtrack: Lp G M root where
 tree:= S.tree
 active:= S.active.bind (fun P=> if h: 0< P.length then some (P.take (P.length-1) (by omega)) else none)
 inside:= by
   intro Q hQ
   cases hP: S.active with
   | none => simp [hP] at hQ
   | some P =>
     simp only [hP,Option.bind_some] at hQ
     split_ifs at hQ with h
     · cases Option.some.inj hQ
       exact P.JJ S.tree.NS (S.inside P hP) _ _
 NU:= S.NU
 modified:= S.modified
 extended:= S.extended
def zS: Lp G M root:= if S.NU|| S.modified then S else S.backtrack
def initial (G M: SimpleGraph (Fin N)) (root: Fin N) (hf:∀w,¬M.Adj root w): Lp G M root where
 tree:= Bi.initial G M root hf
 active:= some (v9.trivial G M root hf)
 inside:= by intro P hP;cases Option.some.inj hP;intro i hi;change i< 2*0 at hi;omega
 NU:= false
 modified:= false
 extended:= false
lemma F5 (ell: ℕ) (labels labels': Fin N ×Fin N→ ℕ) (hS: S.Mq ell labels)
   (hmono:∀a,labels' a≤ labels a): S.Mq ell labels':= by
 intro P hP
 exact P.F5 ell labels labels' (hS P hP) hmono
lemma tP (ell: ℕ) (labels: Fin N ×Fin N→ ℕ) (hS: S.Mq ell labels):
   S.backtrack.Mq ell labels:= by
 intro Q hQ
 change S.active.bind (fun P=> if h: 0< P.length then some (P.take (P.length-1) (by omega)) else none)= some Q at hQ
 cases hP: S.active with
 | none => simp [hP] at hQ
 | some P =>
   simp only [hP,Option.bind_some] at hQ
   split_ifs at hQ with h
   · cases Option.some.inj hQ
     exact P.GR ell labels (hS P hP) _ _
lemma eS (ell: ℕ) (labels: Fin N ×Fin N→ ℕ) (hS: S.Mq ell labels):
   S.zS.Mq ell labels:= by
 unfold zS
 split_ifs
 · exact hS
 · exact S.tP ell labels hS
lemma Ab (G M: SimpleGraph (Fin N)) (root: Fin N) (hf:∀w,¬M.Adj root w)
   (ell: ℕ) (labels: Fin N ×Fin N→ ℕ):(initial G M root hf).Mq ell labels:= by
 intro P hP
 cases Option.some.inj hP
 exact ⟨Nat.zero_le _,fun i hi=> by change i< 0 at hi;omega⟩
lemma oB (ell: ℕ) (labels: Fin N ×Fin N→ ℕ) (hS: S.Mq ell labels):
   S.Dg.card≤ 2*ell+1:= by
 cases hP: S.active with
 | none => simp [Dg,hP]
 | some P =>
   simp only [Dg,hP,Option.elim_some]
   change P.support.card≤ 2*ell+1
   rw [P.IB]
   have hh:=(hS P hP).1
   omega
end Lp
end Be
end
noncomputable section
namespace Be
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)}
   (E: wF G M H K)
lemma C8.Nd (A: Finset (Fin N ×Fin N)) (v: Fin N) (h: C8 M A v):
   C8 K (E.Nc A) (E.toFun v):= by
 obtain ⟨u,w,hArc,hMatch,hV⟩:=h
 refine ⟨E.toFun u,E.toFun w,mem_image.mpr ⟨(u,w),hArc,rfl⟩,
   (E.HS u w).mpr hMatch,?_⟩
 exact hV.imp (congrArg E.toFun) (congrArg E.toFun)
namespace Bi
variable {r: Fin N} (S: Bi G M r)
def Nd: Bi H K (E.toFun r) where
 NS:=E.Nc S.NS
 L9:=E.free_map r S.L9
 valid:=by
   intro a b h
   obtain ⟨⟨u,v⟩,hUV,hEq⟩:=mem_image.mp h
   obtain ⟨rfl,rfl⟩:=Prod.mk.inj hEq
   exact (E.LH u v).mpr (S.valid u v hUV)
 xK:=by
   intro a b hArc hMatch
   obtain ⟨⟨u,v⟩,hUV,hEq⟩:=mem_image.mp hArc
   obtain ⟨rfl,rfl⟩:=Prod.mk.inj hEq
   obtain ⟨Q,hLen,hInside,hTail,hHead⟩:=S.xK u v hUV ((E.HS u v).mp hMatch)
   exact ⟨Q.Nd E,hLen,Q.Ed E S.NS hInside,congrArg E.toFun hTail,congrArg E.toFun hHead⟩
 LD:=by
   intro a b hArc
   obtain ⟨⟨u,v⟩,hUV,hEq⟩:=mem_image.mp hArc
   obtain ⟨rfl,rfl⟩:=Prod.mk.inj hEq
   have hEnds:=S.LD u v hUV
   exact ⟨hEnds.1.imp (congrArg E.toFun) (fun h=>C8.Nd E S.NS u h),
     hEnds.2.imp (congrArg E.toFun) (fun h=>C8.Nd E S.NS v h)⟩
lemma Aj:(S.Nd E).vertices=S.vertices.image E.toFun:= by
 change {E.toFun r}∪(E.Nc S.NS).biUnion (fun a=>{a.1,a.2})=
   ({r}∪S.NS.biUnion (fun a=>{a.1,a.2})).image E.toFun
 unfold wF.Nc
 rw [image_biUnion,image_union,image_singleton,biUnion_image]
 simp only [wF.pairMap,image_insert,image_singleton]
end Bi
namespace Lp
variable {r: Fin N} (S: Lp G M r)
def Nd: Lp H K (E.toFun r) where
 tree:=S.tree.Nd E
 active:=S.active.map (fun Q=>Q.Nd E)
 inside:=by
   intro Q hQ
   obtain ⟨T,hT,hTQ⟩:=Option.map_eq_some_iff.mp hQ
   rw [←hTQ]
   exact T.Ed E S.tree.NS (S.inside T hT)
 NU:=S.NU
 modified:=S.modified
 extended:=S.extended
lemma Aj:(S.Nd E).tree.vertices=S.tree.vertices.image E.toFun:= S.tree.Aj E
end Lp
end Be
end
noncomputable section
namespace Be
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)}
namespace wF
variable (E: wF G M H K)
def inverse (fallback: Fin N) (v: Fin P): Fin N:=
 if h:∃u,E.toFun u=v then h.choose else fallback
lemma inverse_apply (fallback u: Fin N): E.inverse fallback (E.toFun u)=u:= by
 unfold inverse
 have h:∃a,E.toFun a=E.toFun u:=⟨u,rfl⟩
 rw [dif_pos h]
 exact E.injective h.choose_spec
lemma HE (fallback: Fin N) (v: Fin P) (hRange: v∈Set.range E.toFun):
   E.toFun (E.inverse fallback v)=v:= by
 obtain ⟨u,rfl⟩:=hRange
 rw [E.inverse_apply]
lemma f2 (A: Finset (Fin N ×Fin N)) {u v: Fin P}
   (hEdge:(Mv H (E.Nc A)).Adj u v): u∈Set.range E.toFun∧ v∈Set.range E.toFun:= by
 rcases hEdge.2 with hArc|hArc
 · obtain ⟨⟨a,b⟩,hAB,hEq⟩:=mem_image.mp hArc
   obtain ⟨rfl,rfl⟩:=Prod.mk.inj hEq
   exact ⟨⟨a,rfl⟩,⟨b,rfl⟩⟩
 · obtain ⟨⟨a,b⟩,hAB,hEq⟩:=mem_image.mp hArc
   obtain ⟨rfl,rfl⟩:=Prod.mk.inj hEq
   exact ⟨⟨b,rfl⟩,⟨a,rfl⟩⟩
lemma Bn (A: Finset (Fin N ×Fin N)) (r: Fin N)
   (Q: v9 (Mv H (E.Nc A)) K (E.toFun r))
   (i: ℕ) (hi: i≤ 2*Q.length): Q.vertex i∈Set.range E.toFun:= by
 by_cases hZero: i=0
 · rw [hZero,Q.first];exact ⟨r,rfl⟩
 · have hEnds:=E.f2 A (Q.Mu (i-1) (by omega))
   simpa only [Nat.sub_add_cancel (by omega: 1≤ i)] using hEnds.2
end wF
namespace v9
variable (E: wF G M H K) (r: Fin N) (Q: v9 H K (E.toFun r))
   (hRange:∀i,i≤ 2*Q.length→ Q.vertex i∈Set.range E.toFun)
def MS: v9 G M r where
 length:=Q.length
 vertex:=fun i=>E.inverse r (Q.vertex i)
 first:=by rw [Q.first,E.inverse_apply]
 injective:=by
   intro i j hi hj hEq
   apply Q.injective i j hi hj
   have h:=congrArg E.toFun hEq
   rw [E.HE r _ (hRange i hi),E.HE r _ (hRange j hj)] at h
   exact h
 Mu:=by
   intro i hi
   apply (E.LH _ _).mp
   rw [E.HE r _ (hRange i (by omega)),E.HE r _ (hRange (i+1) (by omega))]
   exact Q.Mu i hi
 MG:=by
   intro i hi
   rw [←E.HS]
   rw [E.HE r _ (hRange i (by omega)),E.HE r _ (hRange (i+1) (by omega))]
   exact Q.MG i hi
 L9:=by
   intro v hMatch
   exact Q.L9 (E.toFun v) ((E.HS r v).mpr hMatch)
lemma Cu (i: ℕ) (hi: i≤ 2*Q.length):
   E.toFun ((Q.MS E r hRange).vertex i)=Q.vertex i:=E.HE r _ (hRange i hi)
lemma sK (i: ℕ) (hi: i< Q.length):
   E.pairMap ((Q.MS E r hRange).KA i)=Q.KA i:= by
 apply Prod.ext
 · exact Q.Cu E r hRange (2*i+1) (by omega)
 · exact Q.Cu E r hRange (2*i+2) (by omega)
lemma Ct (A: Finset (Fin N ×Fin N)) (hInside: Q.Nv (E.Nc A)):
   (Q.MS E r hRange).Nv A:= by
 intro i hi
 change i< 2*Q.length at hi
 apply (E.Jn A _ _).mp
 rw [Q.Cu E r hRange i (by omega),Q.Cu E r hRange (i+1) (by omega)]
 exact hInside i hi
end v9
namespace Bi
variable (E: wF G M H K) {r: Fin N} (S: Bi G M r)
lemma Ag (hComplete: S.qK):(S.Nd E).qK:= by
 intro Q i hi
 have hRange:=E.Bn S.NS r Q
 let L:=Q.MS (E.NH S.NS) r hRange
 have hInside:=(hComplete L) i hi
 have hMap:(E.toFun (L.vertex i),E.toFun (L.vertex (i+1)))∈E.Nc S.NS:=
   mem_image.mpr ⟨(L.vertex i,L.vertex (i+1)),hInside,rfl⟩
 have hI:=Q.Cu (E.NH S.NS) r hRange i (by omega)
 have hJ:=Q.Cu (E.NH S.NS) r hRange (i+1) (by omega)
 change E.toFun (L.vertex i)=Q.vertex i at hI
 change E.toFun (L.vertex (i+1))=Q.vertex (i+1) at hJ
 rw [hI,hJ] at hMap
 exact hMap
end Bi
end Be
end
noncomputable section
namespace JW
def merge {I: Type} (own: Finset (ℕ ×I)) (msgs: Multiset (Finset (ℕ ×I))): Finset (ℕ ×I):=
 own ∪msgs.toFinset.biUnion id
section Flood
variable {V I: Type} [Fintype V] (H: SimpleGraph V) (ids: V→ ℕ) (inp: V→ I)
def NK: ℕ→ V→ Finset (ℕ ×I)
 | 0,v => {(ids v,inp v)}
 | t+1,v => merge (NK t v) ((H.neighborFinset v).val.map (NK t))
lemma Kl (t: ℕ) (v: V):(ids v,inp v)∈ NK H ids inp t v:= by
 induction t with
 | zero => exact mem_singleton_self _
 | succ t ih => exact mem_union_left _ ih
lemma DM (t: ℕ) (v u: V) (hvu: H.Adj v u):
   NK H ids inp t u ⊆NK H ids inp (t+1) v:= by
 intro r hr
 apply mem_union_right
 apply mem_biUnion.mpr
 refine ⟨NK H ids inp t u,?_,hr⟩
 apply Multiset.mem_toFinset.mpr
 exact Multiset.mem_map.mpr ⟨u,(SimpleGraph.mem_neighborFinset H v u).mpr hvu,rfl⟩
lemma BL (t: ℕ) (v: V):∀r∈ NK H ids inp t v,∃u,r=(ids u,inp u):= by
 induction t generalizing v with
 | zero =>
   intro r hr
   exact ⟨v,mem_singleton.mp hr⟩
 | succ t ih =>
   intro r hr
   rcases mem_union.mp hr with hr|hr
   · exact ih v r hr
   · obtain ⟨S,hS,hr⟩:= mem_biUnion.mp hr
     obtain ⟨u,hu,he⟩:= Multiset.mem_map.mp (Multiset.mem_toFinset.mp hS)
     subst S
     exact ih u r hr
lemma Km (t: ℕ) {v u: V} (w: H.Walk v u) (hw: w.length≤ t):
   (ids u,inp u)∈ NK H ids inp t v:= by
 induction t generalizing v with
 | zero =>
   have he: v= u:= by
     have hz: w.length= 0:= by omega
     exact (SimpleGraph.Walk.length_eq_zero_iff.mp hz).eq
   subst u
   exact Kl H ids inp 0 v
 | succ t ih =>
   cases w with
   | nil => exact Kl H ids inp (t+1) _
   | @cons v u z h w =>
     exact DM H ids inp t v u h (ih w (by simpa using hw))
lemma I8 (t: ℕ) (v u: V) (hc: Close H t v u):
   (ids u,inp u)∈ NK H ids inp t v:= by
 obtain ⟨w,hw⟩:= hc
 exact Km H ids inp t w hw
end Flood
end JW
end
noncomputable section
namespace Be
variable {V I: Type} [Fintype V]
def Mc (G: SimpleGraph V) (label: V→ ℕ): SimpleGraph V where
 Adj u v:= G.Adj u v∧ label u= label v
 symm:=⟨by rintro u v ⟨h,he⟩;exact ⟨h.symm,he.symm⟩⟩
 loopless:=⟨by rintro v ⟨h,_⟩;exact h.ne rfl⟩
lemma sV (G: SimpleGraph V) (label: V→ ℕ) (u v: V)
   (h:(Mc G label).Reachable u v): label u= label v:= by
 obtain ⟨w⟩:= h
 induction w with
 | nil => rfl
 | cons h w ih => exact h.2.trans ih
lemma CI (G: SimpleGraph V) (label: V→ ℕ) (s: ℕ) (u v: V)
   (h:(Mc G label).Reachable u v)
   (hc:(univ.filter (fun w=> label w= label u)).card≤ s):
   Close (Mc G label) s u v:= by
 obtain ⟨w,hpath,hlen⟩:= h.exists_path_of_dist
 have hsub: w.support.toFinset ⊆univ.filter (fun z=> label z= label u):= by
   intro z hz
   have hz':= List.mem_toFinset.mp hz
   have hr:(Mc G label).Reachable u z:=⟨w.takeUntil z hz'⟩
   exact mem_filter.mpr ⟨mem_univ _,(sV G label u z hr).symm⟩
 have hcard:=(card_le_card hsub).trans hc
 rw [List.toFinset_card_of_nodup hpath.support_nodup,SimpleGraph.Walk.length_support] at hcard
 exact ⟨w,by omega⟩
lemma qY (G: SimpleGraph V) (label: V→ ℕ) (f: V→ Finset (ℕ ×I)) (v: V):
   ((((G.neighborFinset v).val.map (fun w=>(label w,f w))).filter (fun m=> m.1= label v)).map Prod.snd)=
     ((Mc G label).neighborFinset v).val.map f:= by
 have heq:(G.neighborFinset v).filter (fun w=> label w= label v)=(Mc G label).neighborFinset v:= by
   ext w
   simp only [mem_filter,SimpleGraph.mem_neighborFinset]
   change (G.Adj v w∧ label w= label v)↔ G.Adj v w∧ label v= label w
   tauto
 rw [Multiset.filter_map,Multiset.map_map]
 change (((G.neighborFinset v).val.filter (fun w=> label w= label v)).map f)= _
 rw [←Finset.filter_val,heq]
def collect (I: Type): Deterministic ℕ (ℕ ×I) (Finset (ℕ ×I)) where
 program:={
   State:= ℕ ×Finset (ℕ ×I)
   Msg:= ℕ ×Finset (ℕ ×I)
   rounds:= id
   init:= fun _ id inp _=>(inp.1,{(id,inp.2)})
   send:= id
   step:= fun st msgs=>(st.1,JW.merge st.2 ((msgs.filter (fun msg=> msg.1= st.1)).map Prod.snd))
   out:= Prod.snd}
 tape_independent:= by intros;rfl
lemma I1 (G: SimpleGraph V) (label ids: V→ ℕ) (inp: V→ I) (r t: ℕ):∀v,
   (collect I).program.run G r ids (fun v=>(label v,inp v)) (fun _ _=> false) t v=
     (label v,JW.NK (Mc G label) ids inp t v):= by
 induction t with
 | zero => intro v;rfl
 | succ t ih =>
   intro v
   conv_lhs=> rw [SmoothedMIS.LocalAlg.run]
   simp only [ih]
   have hn: univ.filter (G.Adj v)= G.neighborFinset v:= by ext w;simp
   change (label v,JW.merge (JW.NK (Mc G label) ids inp t v)
     (((((univ.filter (G.Adj v)).val.map (fun w=>(label w,JW.NK (Mc G label) ids inp t w))).filter
       (fun msg=> msg.1= label v)).map Prod.snd)))= _
   rw [hn,qY]
   rfl
lemma BM (H: SimpleGraph V) (ids: V→ ℕ) (inp: V→ I) (t: ℕ) (v: V):
   ∀r∈ JW.NK H ids inp t v,∃u,H.Reachable v u∧ r=(ids u,inp u):= by
 induction t generalizing v with
 | zero =>
   intro r hr
   exact ⟨v,SimpleGraph.Reachable.refl _,mem_singleton.mp hr⟩
 | succ t ih =>
   intro r hr
   rcases mem_union.mp hr with hr|hr
   · exact ih v r hr
   · obtain ⟨S,hS,hr⟩:= mem_biUnion.mp hr
     obtain ⟨u,hu,heq⟩:= Multiset.mem_map.mp (Multiset.mem_toFinset.mp hS)
     subst S
     obtain ⟨w,hw,heq⟩:= ih u r hr
     exact ⟨w,((H.mem_neighborFinset v u).mp hu).reachable.trans hw,heq⟩
lemma By (G: SimpleGraph V) (label ids: V→ ℕ) (inp: V→ I) (s: ℕ)
   (hconnected:∀u v,label u= label v→(Mc G label).Reachable u v)
   (hsize:∀v,(univ.filter (fun w=> label w= label v)).card≤ s) (v: V):
   (collect I).program.output G s ids (fun v=>(label v,inp v)) (fun _ _=> false) v=
     (univ.filter (fun w=> label w= label v)).image (fun w=>(ids w,inp w)):= by
 unfold SmoothedMIS.LocalAlg.output
 rw [show (collect I).program.rounds s= s from rfl,I1]
 change JW.NK (Mc G label) ids inp s v= _
 ext r
 constructor
 · intro hr
   obtain ⟨u,hu,heq⟩:= BM (Mc G label) ids inp s v r hr
   exact mem_image.mpr ⟨u,mem_filter.mpr ⟨mem_univ _,(sV G label v u hu).symm⟩,heq.symm⟩
 · intro hr
   obtain ⟨u,hu,rfl⟩:= mem_image.mp hr
   have heq:=(mem_filter.mp hu).2
   have hclose:= CI G label s v u (hconnected v u heq.symm) (hsize v)
   exact JW.I8 (Mc G label) ids inp s v u hclose
end Be
end
noncomputable section
namespace Be
variable {N: ℕ}
structure tE (G: SimpleGraph (Fin N)) (s: ℕ) where
 leader: Fin N→ Fin N
 fixed:∀v,leader (leader v)= leader v
 connected:∀u v,leader u= leader v→(Mc G (fun w=>(leader w).val)).Reachable u v
 small:∀v,(univ.filter (fun w=> leader w= leader v)).card≤ s
namespace tE
variable {G: SimpleGraph (Fin N)} {s: ℕ} (P: tE G s)
lemma Jt (v: Fin N): Close G s (P.leader v) v:= by
 have hconn:= P.connected (P.leader v) v (P.fixed v)
 have hsize:(univ.filter (fun w=>(P.leader w).val=(P.leader (P.leader v)).val)).card≤ s:= by
   simp only [P.fixed,Fin.val_inj]
   exact P.small v
 obtain ⟨w,hw⟩:= CI G (fun w=>(P.leader w).val) s (P.leader v) v hconn hsize
 have hle: Mc G (fun w=>(P.leader w).val)≤ G:= fun _ _ h=> h.1
 exact ⟨w.mapLe hle,by simpa using hw⟩
def Lv (Lx: Fin N→ Fin N→ Prop) (hC: Symmetric Lx): SimpleGraph (Fin N) where
 Adj a b:= P.leader a= a∧ P.leader b= b∧ a≠ b∧
   ∃u v,P.leader u= a∧ P.leader v= b∧ G.Adj u v∧ Lx u v
 symm:=⟨by
   rintro a b ⟨ha,hb,hne,u,v,hu,hv,hG,hcand⟩
   exact ⟨hb,ha,hne.symm,v,u,hv,hu,hG.symm,hC hcand⟩⟩
 loopless:=⟨by rintro a ⟨_,_,h,_⟩;exact h rfl⟩
lemma Bp (Lx: Fin N→ Fin N→ Prop) (hC: Symmetric Lx)
   (a b: Fin N) (hab:(P.Lv Lx hC).Adj a b): Close G (2*s+1) a b:= by
 obtain ⟨ha,hb,hne,u,v,hu,hv,hG,hcand⟩:= hab
 obtain ⟨left,hl⟩:=(show Close G s a u from by simpa only [hu] using P.Jt u)
 obtain ⟨right,hr⟩:=(show Close G s b v from by simpa only [hv] using P.Jt v)
 refine ⟨left.append (hG.toWalk.append right.reverse),?_⟩
 simp only [SimpleGraph.Walk.length_append,SimpleGraph.Adj.toWalk,SimpleGraph.Walk.length_cons,SimpleGraph.Walk.length_nil,SimpleGraph.Walk.length_reverse]
 omega
lemma zR (Lx: Fin N→ Fin N→ Prop) (hC: Symmetric Lx)
   (D: ℕ) (hD:∀v,G.degree v≤ D) (a: Fin N):
   (P.Lv Lx hC).degree a≤ s*D:= by
 by_cases ha: P.leader a= a
 · let S:= univ.filter (fun u=> P.leader u= a)
   have hS: S.card≤ s:= by simpa only [ha] using P.small a
   have hsub:(P.Lv Lx hC).neighborFinset a ⊆S.biUnion (fun u=>(G.neighborFinset u).image P.leader):= by
     intro b hb
     obtain ⟨_,_,_,u,v,hu,hv,hG,_⟩:=((P.Lv Lx hC).mem_neighborFinset a b).mp hb
     exact mem_biUnion.mpr ⟨u,mem_filter.mpr ⟨mem_univ _,hu⟩,
       mem_image.mpr ⟨v,(G.mem_neighborFinset u v).mpr hG,hv⟩⟩
   rw [←SimpleGraph.card_neighborFinset_eq_degree]
   calc
     _≤(S.biUnion (fun u=>(G.neighborFinset u).image P.leader)).card:= card_le_card hsub
     _≤∑u∈ S,((G.neighborFinset u).image P.leader).card:= card_biUnion_le
     _≤∑u∈ S,D:= sum_le_sum (fun u _=>(card_image_le).trans (by simpa using hD u))
     _= S.card*D:= by simp [mul_comm]
     _≤ s*D:= Nat.mul_le_mul_right D hS
 · have he:(P.Lv Lx hC).neighborFinset a=∅:= by
     apply eq_empty_iff_forall_notMem.mpr
     intro b hb
     exact ha (((P.Lv Lx hC).mem_neighborFinset a b).mp hb).1
   rw [←SimpleGraph.card_neighborFinset_eq_degree,he,card_empty]
   omega
end tE
end Be
end
noncomputable section
namespace Be
variable {V: Type} [Fintype V] [DecidableEq V]
def Ni (ids: V→ ℕ) (hi: Function.Injective ids) (M: SimpleGraph V) (v: V): V:=
 (tB.NW ids hi M v).getD v
lemma vA (ids: V→ ℕ) (hi: Function.Injective ids) (M: SimpleGraph V)
   (hM:∀u v w,M.Adj u v→ M.Adj u w→ v= w): Function.Involutive (Ni ids hi M):= by
 intro v
 cases hm: tB.NW ids hi M v with
 | none => simp only [Ni,hm,Option.getD_none]
 | some w =>
   have hvw:=(tB.LW ids hi M hM v w).mp hm
   have hmv:=(tB.LW ids hi M hM w v).mpr hvw.symm
   simp only [Ni,hm,Option.getD_some,hmv]
lemma x7 (ids: V→ ℕ) (hi: Function.Injective ids) (M: SimpleGraph V) (v: V):
   Ni ids hi M v= v∨ M.Adj v (Ni ids hi M v):= by
 cases hm: tB.NW ids hi M v with
 | none => exact Or.inl (by simp [Ni,hm])
 | some w =>
   right
   have hvw:=(SimpleGraph.mem_neighborFinset M v w).mp (tB.LQ ids hi _ w hm)
   simpa only [Ni,hm,Option.getD_some] using hvw
def representative (ids: V→ ℕ) (f: V→ V) (v: V): V:= if ids v≤ ids (f v) then v else f v
lemma k9 (ids: V→ ℕ) (hi: Function.Injective ids) (f: V→ V)
   (hf: Function.Involutive f) (v: V): representative ids f (f v)= representative ids f v:= by
 by_cases h: ids v≤ ids (f v)
 · by_cases h': ids (f v)≤ ids v
   · have heq: f v= v:= hi (le_antisymm h' h)
     simp only [representative,hf v,heq,le_refl,if_true]
   · simp only [representative,hf v,if_neg h',if_pos h]
 · have h': ids (f v)≤ ids v:= le_of_not_ge h
   simp only [representative,hf v,if_pos h',if_neg h]
lemma yI (ids: V→ ℕ) (hi: Function.Injective ids) (f: V→ V)
   (hf: Function.Involutive f) (v w: V):
   representative ids f v= representative ids f w↔ w= v∨ w= f v:= by
 constructor
 · intro h
   unfold representative at h
   split_ifs at h with hv hw hw
   · exact Or.inl h.symm
   · have hh:= congrArg f h
     rw [hf w] at hh
     exact Or.inr hh.symm
   · exact Or.inr h.symm
   · have hh:= congrArg f h
     rw [hf v,hf w] at hh
     exact Or.inl hh.symm
 · rintro (rfl|rfl)
   · rfl
   · exact (k9 ids hi f hf v).symm
lemma pR (ids: V→ ℕ) (hi: Function.Injective ids) (f: V→ V)
   (hf: Function.Involutive f) (v: V):
   representative ids f (representative ids f v)= representative ids f v:= by
 change representative ids f (if ids v≤ ids (f v) then v else f v)=(if ids v≤ ids (f v) then v else f v)
 by_cases h: ids v≤ ids (f v)
 · rw [if_pos h]
   exact if_pos h
 · rw [if_neg h]
   exact (k9 ids hi f hf v).trans (if_neg h)
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G: SimpleGraph (Fin N)} {s: ℕ}
namespace tE
variable (P: tE G s) (Lx: Fin N→ Fin N→ Prop) (hC: Symmetric Lx)
   (R: SimpleGraph (Fin N)) (hR: Matching (P.Lv Lx hC) R)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids)
def HY (v: Fin N): Fin N:= representative ids (Ni ids hi R) (P.leader v)
include hR in
lemma pairMap_involutive: Function.Involutive (Ni ids hi R):=
 vA ids hi R (qJ.gP _ R hR)
include hR in
lemma Ic (v: Fin N) (hv: P.leader v= v):
   P.leader (Ni ids hi R v)= Ni ids hi R v:= by
 rcases x7 ids hi R v with h| h
 · rw [h]
   exact hv
 · exact (hR.1 h).2.1
include hR in
lemma sO (v: Fin N):
   P.leader (representative ids (Ni ids hi R) (P.leader v))= representative ids (Ni ids hi R) (P.leader v):= by
 unfold representative
 split_ifs
 · exact P.fixed v
 · exact P.Ic Lx hC R hR ids hi (P.leader v) (P.fixed v)
include hR in
lemma HZ (v: Fin N):
   P.HY R ids hi (P.HY R ids hi v)= P.HY R ids hi v:= by
 change representative ids (Ni ids hi R) (P.leader (representative ids (Ni ids hi R) (P.leader v)))= _
 rw [P.sO Lx hC R hR ids hi]
 exact pR ids hi _ (P.pairMap_involutive Lx hC R hR ids hi) _
lemma Gm: Mc G (fun v=>(P.leader v).val)≤ Mc G (fun v=>(P.HY R ids hi v).val):= by
 intro u v h
 refine ⟨h.1,?_⟩
 have heq: P.leader u= P.leader v:= Fin.ext h.2
 exact congrArg Fin.val (congrArg (representative ids (Ni ids hi R)) heq)
include hR in
lemma Ar (u v: Fin N) (huv: P.HY R ids hi u= P.HY R ids hi v):
   (Mc G (fun w=>(P.HY R ids hi w).val)).Reachable u v:= by
 have hmap:= P.Gm R ids hi
 have old (a b: Fin N) (hab: P.leader a= P.leader b):
     (Mc G (fun w=>(P.HY R ids hi w).val)).Reachable a b:= by
   obtain ⟨w⟩:= P.connected a b hab
   exact ⟨w.mapLe hmap⟩
 have hf:= P.pairMap_involutive Lx hC R hR ids hi
 rcases (yI ids hi _ hf (P.leader u) (P.leader v)).mp huv with heq| heq
 · exact old u v heq.symm
 · rcases x7 ids hi R (P.leader u) with hfix| hadj
   · exact old u v (heq.trans hfix).symm
   · obtain ⟨_,_,_,x,y,hx,hy,hxy,_⟩:= hR.1 hadj
     have hx': P.leader u= P.leader x:= hx.symm
     have hy': P.leader y= P.leader v:= hy.trans heq.symm
     have hn: P.HY R ids hi x= P.HY R ids hi y:= by
       change representative ids _ (P.leader x)= representative ids _ (P.leader y)
       rw [hx,hy]
       exact (k9 ids hi _ hf (P.leader u)).symm
     have hc:(Mc G (fun w=>(P.HY R ids hi w).val)).Adj x y:=
       ⟨hxy,congrArg Fin.val hn⟩
     exact (old u x hx').trans (hc.reachable.trans (old y v hy'))
include hR in
lemma H0 (v: Fin N):
   (univ.filter (fun w=> P.HY R ids hi w= P.HY R ids hi v)).card≤ 2*s:= by
 let S:= univ.filter (fun w=> P.leader w= P.leader v)
 let T:= univ.filter (fun w=> P.leader w= Ni ids hi R (P.leader v))
 have hS: S.card≤ s:= P.small v
 have hfRoot:= P.Ic Lx hC R hR ids hi (P.leader v) (P.fixed v)
 have hT: T.card≤ s:= by simpa only [hfRoot] using P.small (Ni ids hi R (P.leader v))
 have hsub: univ.filter (fun w=> P.HY R ids hi w= P.HY R ids hi v) ⊆S ∪T:= by
   intro w hw
   have hh:=(mem_filter.mp hw).2
   have hf:= P.pairMap_involutive Lx hC R hR ids hi
   rcases (yI ids hi _ hf (P.leader v) (P.leader w)).mp hh.symm with h| h
   · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨mem_univ _,h⟩))
   · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨mem_univ _,h⟩))
 exact (card_le_card hsub).trans ((card_union_le S T).trans (by omega))
include hR in
noncomputable def merge: tE G (2*s) where
 leader:= P.HY R ids hi
 fixed:= P.HZ Lx hC R hR ids hi
 connected:= P.Ar Lx hC R hR ids hi
 small:= P.H0 Lx hC R hR ids hi
end tE
end Be
end
noncomputable section
namespace Be
variable {I: Type}
def lookup (R: Finset (ℕ ×I)) (j: ℕ): Option I:=
 if h:∃x,(j,x)∈ R then some h.choose else none
lemma Ea {V: Type} (R: Finset (ℕ ×I)) (ids: V→ ℕ) (inp: V→ I)
   (hi: Function.Injective ids) (hauth:∀r∈ R,∃v,r=(ids v,inp v)) (v: V)
   (hmem:(ids v,inp v)∈ R): lookup R (ids v)= some (inp v):= by
 unfold lookup
 have hex:∃x,(ids v,x)∈ R:=⟨inp v,hmem⟩
 rw [dif_pos hex]
 congr 1
 obtain ⟨w,hw⟩:= hauth _ hex.choose_spec
 have heq: v= w:= hi (congrArg Prod.fst hw)
 subst w
 exact congrArg Prod.snd hw
def IH (label: ℕ) (report: Option ℕ): ℕ:= match report with
 | none => label
 | some j => min label j
lemma GA {N: ℕ} (G M: SimpleGraph (Fin N)) (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (out: Fin N→ Option ℕ) (hout: ReportsMatching G ids out M) (v: Fin N):
   out v=(tB.NW ids hi M v).map ids:= by
 have hM:= qJ.gP G M hout.1
 cases hm: tB.NW ids hi M v with
 | none => exact (hout.2 v).1.mpr ((tB.LV ids hi M v).mp hm)
 | some w => exact ((hout.2 v).2 (ids w)).mpr ⟨w,(tB.LW ids hi M hM v w).mp hm,rfl⟩
lemma qE {N: ℕ} (G M: SimpleGraph (Fin N)) (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (out: Fin N→ Option ℕ) (hout: ReportsMatching G ids out M) (v: Fin N):
   IH (ids v) (out v)= ids (representative ids (Ni ids hi M) v):= by
 rw [GA G M ids hi out hout v]
 cases hm: tB.NW ids hi M v with
 | none => simp [IH,representative,Ni,hm]
 | some w =>
   simp only [Option.map_some,IH,Ni,hm,Option.getD_some,representative]
   by_cases h: ids v≤ ids w
   · rw [if_pos h,min_eq_left h]
   · rw [if_neg h,min_eq_right (le_of_not_ge h)]
namespace tE
variable {N: ℕ} {G: SimpleGraph (Fin N)} {s: ℕ} (P: tE G s)
lemma I0 (ids: Fin N→ ℕ) (hi: Function.Injective ids) (inp: Fin N→ I) (v: Fin N):
   (collect I).program.output G s ids (fun v=>(ids (P.leader v),inp v)) (fun _ _=> false) v=
     (univ.filter (fun w=> P.leader w= P.leader v)).image (fun w=>(ids w,inp w)):= by
 have hle: Mc G (fun v=>(P.leader v).val)≤ Mc G (fun v=> ids (P.leader v)):= by
   intro u v h
   exact ⟨h.1,congrArg ids (Fin.ext h.2)⟩
 have hc (u v: Fin N) (he: ids (P.leader u)= ids (P.leader v)):
     (Mc G (fun v=> ids (P.leader v))).Reachable u v:= by
   obtain ⟨w⟩:= P.connected u v (hi he)
   exact ⟨w.mapLe hle⟩
 have hs (v: Fin N):(univ.filter (fun w=> ids (P.leader w)= ids (P.leader v))).card≤ s:= by
   simpa only [hi.eq_iff] using P.small v
 simpa only [hi.eq_iff] using By G (fun v=> ids (P.leader v)) ids inp s hc hs v
end tE
end Be
end
noncomputable section
namespace Be
abbrev J2:= Finset ℕ ×Option ℕ
abbrev y6:= Finset (ℕ ×J2)
namespace y6
def keys (D: y6): Finset ℕ:=D.image Prod.fst
def enumerate (D: y6): Fin D.keys.card ≃D.keys:=
 (Fintype.equivFinOfCardEq (Fintype.card_coe D.keys)).symm
def identity (D: y6) (i: Fin D.keys.card): ℕ:=(D.enumerate i).val
lemma Hy (D: y6) (i: Fin D.keys.card): D.identity i∈D.keys:=(D.enumerate i).property
lemma identity_injective (D: y6): Function.Injective D.identity:= by
 intro i j h
 apply D.enumerate.injective
 exact Subtype.ext h
lemma rF (D: y6) (j: ℕ) (hj: j∈D.keys):
   ∃i,D.identity i=j:= by
 refine ⟨D.enumerate.symm ⟨j,hj⟩,?_⟩
 exact congrArg Subtype.val (D.enumerate.apply_symm_apply ⟨j,hj⟩)
def neighbors (D: y6) (j: ℕ): Finset ℕ:=((lookup D j).map Prod.fst).getD ∅
def NW (D: y6) (j: ℕ): Option ℕ:=(lookup D j).bind Prod.snd
def JS (D: y6): Prop:=∀a∈D,∀b∈D,a.1=b.1→ a=b
def JX (D: y6): Prop:=∀j∈D.keys,∀k,D.NW j=some k→ k∈D.keys
def graph (D: y6): SimpleGraph (Fin D.keys.card) where
 Adj u v:=u≠v∧ D.identity v∈D.neighbors (D.identity u)∧ D.identity u∈D.neighbors (D.identity v)
 symm:=⟨by rintro u v ⟨hNe,hUV,hVU⟩;exact ⟨hNe.symm,hVU,hUV⟩⟩
 loopless:=⟨fun _ h=>h.1 rfl⟩
def MG (D: y6): SimpleGraph (Fin D.keys.card) where
 Adj u v:=D.graph.Adj u v∧ D.NW (D.identity u)=some (D.identity v)∧ D.NW (D.identity v)=some (D.identity u)
 symm:=⟨by rintro u v ⟨hEdge,hUV,hVU⟩;exact ⟨hEdge.symm,hVU,hUV⟩⟩
 loopless:=⟨fun _ h=>h.1.ne rfl⟩
lemma Eg (D: y6): Matching D.graph D.MG:= by
 apply tB.n4
 · intro u v h;exact h.1
 · intro u v w hUV hUW
   apply D.identity_injective
   exact Option.some.inj (hUV.2.1.symm.trans hUW.2.1)
variable {N: ℕ}
def Li (D: y6) (G: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (out: Fin N→ Option ℕ): Prop:=
 ∀z∈D,∃v,z=(ids v,(neighborIDs G ids v,out v))
lemma Fv (D: y6) {G: SimpleGraph (Fin N)} {ids: Fin N→ ℕ}
   {out: Fin N→ Option ℕ} (hAuth: D.Li G ids out) (j: ℕ) (hj: j∈D.keys):
   ∃v,ids v=j:= by
 obtain ⟨z,hz,hId⟩:=mem_image.mp hj
 obtain ⟨v,hV⟩:=hAuth z hz
 exact ⟨v,(congrArg Prod.fst hV).symm.trans hId⟩
lemma zQ (D: y6) {G: SimpleGraph (Fin N)} {ids: Fin N→ ℕ}
   {out: Fin N→ Option ℕ} (hi: Function.Injective ids) (hAuth: D.Li G ids out)
   (v: Fin N) (hKey: ids v∈D.keys):(ids v,(neighborIDs G ids v,out v))∈D:= by
 obtain ⟨z,hz,hId⟩:=mem_image.mp hKey
 obtain ⟨u,hU⟩:=hAuth z hz
 have hUV: u=v:=hi ((congrArg Prod.fst hU).symm.trans hId)
 rw [hUV] at hU
 exact hU ▸hz
lemma zP (D: y6) {G: SimpleGraph (Fin N)} {ids: Fin N→ ℕ}
   {out: Fin N→ Option ℕ} (hi: Function.Injective ids) (hAuth: D.Li G ids out)
   (v: Fin N) (hKey: ids v∈D.keys): lookup D (ids v)=some (neighborIDs G ids v,out v):=
 Ea D ids (fun v=>(neighborIDs G ids v,out v)) hi hAuth v (D.zQ hi hAuth v hKey)
lemma qS (D: y6) {G: SimpleGraph (Fin N)} {ids: Fin N→ ℕ}
   {out: Fin N→ Option ℕ} (hi: Function.Injective ids) (hAuth: D.Li G ids out)
   (v: Fin N) (hKey: ids v∈D.keys): D.neighbors (ids v)=neighborIDs G ids v:= by
 unfold neighbors
 rw [D.zP hi hAuth v hKey]
 rfl
lemma Dj (D: y6) {G: SimpleGraph (Fin N)} {ids: Fin N→ ℕ}
   {out: Fin N→ Option ℕ} (hi: Function.Injective ids) (hAuth: D.Li G ids out)
   (v: Fin N) (hKey: ids v∈D.keys): D.NW (ids v)=out v:= by
 unfold NW
 rw [D.zP hi hAuth v hKey]
 rfl
end y6
end Be
end
noncomputable section
namespace Be
variable {N: ℕ}
lemma rX (G: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (hi: Function.Injective ids) (u v: Fin N): ids v∈neighborIDs G ids u↔ G.Adj u v:= by
 constructor
 · intro h
   obtain ⟨w,hw,hId⟩:=mem_image.mp h
   have hWV: w=v:=hi hId
   subst w
   exact (G.mem_neighborFinset u v).mp hw
 · intro h
   exact mem_image.mpr ⟨v,(G.mem_neighborFinset u v).mpr h,rfl⟩
lemma CB (G M: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (hi: Function.Injective ids) (out: Fin N→ Option ℕ)
   (hOut: ReportsMatching G ids out M) (u v: Fin N): out u=some (ids v)↔ M.Adj u v:= by
 constructor
 · intro h
   obtain ⟨w,hw,hId⟩:=((hOut.2 u).2 (ids v)).mp h
   have hWV: w=v:=hi hId
   exact hWV ▸hw
 · intro h;exact ((hOut.2 u).2 (ids v)).mpr ⟨v,h,rfl⟩
namespace y6
variable (D: y6) {G M: SimpleGraph (Fin N)} {ids: Fin N→ ℕ}
   {out: Fin N→ Option ℕ} (hAuth: D.Li G ids out)
def MQ (i: Fin D.keys.card): Fin N:=(D.Fv hAuth (D.identity i) (D.Hy i)).choose
lemma yA (i: Fin D.keys.card): ids (D.MQ hAuth i)=D.identity i:=
 (D.Fv hAuth (D.identity i) (D.Hy i)).choose_spec
lemma vH (hi: Function.Injective ids): Function.Injective (D.MQ hAuth):= by
 intro i j h
 apply D.identity_injective
 rw [←D.yA hAuth i,←D.yA hAuth j,h]
lemma Ih (i: Fin D.keys.card): ids (D.MQ hAuth i)∈D.keys:= by
 rw [D.yA hAuth]
 exact D.Hy i
lemma vG (hi: Function.Injective ids) (u v: Fin D.keys.card):
   G.Adj (D.MQ hAuth u) (D.MQ hAuth v)↔ D.graph.Adj u v:= by
 change G.Adj (D.MQ hAuth u) (D.MQ hAuth v)↔
   u≠v∧ D.identity v∈D.neighbors (D.identity u)∧ D.identity u∈D.neighbors (D.identity v)
 rw [←D.yA hAuth u,←D.yA hAuth v,
   D.qS hi hAuth _ (D.Ih hAuth u),
   D.qS hi hAuth _ (D.Ih hAuth v),
   rX G ids hi,rX G ids hi]
 constructor
 · intro h
   exact ⟨fun hEq=>h.ne (congrArg (D.MQ hAuth) hEq),h,h.symm⟩
 · exact fun h=>h.2.1
lemma nL (hi: Function.Injective ids) (hOut: ReportsMatching G ids out M)
   (u v: Fin D.keys.card):
   M.Adj (D.MQ hAuth u) (D.MQ hAuth v)↔ D.MG.Adj u v:= by
 change M.Adj (D.MQ hAuth u) (D.MQ hAuth v)↔
   D.graph.Adj u v∧ D.NW (D.identity u)=some (D.identity v)∧ D.NW (D.identity v)=some (D.identity u)
 rw [←D.vG hAuth hi,
   ←D.yA hAuth u,←D.yA hAuth v,
   D.Dj hi hAuth _ (D.Ih hAuth u),
   D.Dj hi hAuth _ (D.Ih hAuth v),
   CB G M ids hi out hOut,CB G M ids hi out hOut]
 exact ⟨fun h=>⟨hOut.1.1 h,h,h.symm⟩,fun h=>h.2.1⟩
def embedding (hi: Function.Injective ids) (hOut: ReportsMatching G ids out M) (hClosed: D.JX):
   wF D.graph D.MG G M where
 toFun:=D.MQ hAuth
 injective:=D.vH hAuth hi
 LH:=D.vG hAuth hi
 HS:=D.nL hAuth hi hOut
 B7:=by
   intro u w hMatch
   have hSome:=((hOut.2 (D.MQ hAuth u)).2 (ids w)).mpr ⟨w,hMatch,rfl⟩
   have hMate: D.NW (D.identity u)=some (ids w):= by
     rw [←D.yA hAuth u,D.Dj hi hAuth _ (D.Ih hAuth u)]
     exact hSome
   have hKey:=hClosed (D.identity u) (D.Hy u) (ids w) hMate
   obtain ⟨v,hV⟩:=D.rF (ids w) hKey
   refine ⟨v,?_⟩
   exact hi ((D.yA hAuth v).trans hV)
end y6
end Be
end
noncomputable section
namespace Be
variable {N P Q: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)} {L R: SimpleGraph (Fin Q)}
namespace wF
def comp (E: wF G M H K) (F: wF H K L R): wF G M L R where
 toFun:=fun u=>F.toFun (E.toFun u)
 injective:=F.injective.comp E.injective
 LH:=fun u v=>(F.LH _ _).trans (E.LH u v)
 HS:=fun u v=>(F.HS _ _).trans (E.HS u v)
 B7:=by
   intro u w hEdge
   obtain ⟨v,hV⟩:=F.B7 (E.toFun u) w hEdge
   have hMid: K.Adj (E.toFun u) v:=(F.HS _ _).mp (by rw [hV];exact hEdge)
   obtain ⟨a,hA⟩:=E.B7 u v hMid
   exact ⟨a,(congrArg F.toFun hA).trans hV⟩
lemma DG (E F: wF G M H K) (h: E.toFun=F.toFun): E=F:= by
 cases E
 cases F
 cases h
 rfl
end wF
namespace v9
lemma Kd {r: Fin N} (A B: v9 G M r) (hLength: A.length=B.length)
   (hVertex: A.vertex=B.vertex): A=B:= by
 cases A
 cases B
 cases hLength
 cases hVertex
 rfl
lemma HM (E: wF G M H K) (F: wF H K L R)
   {r: Fin N} (A: v9 G M r):(A.Nd E).Nd F=A.Nd (E.comp F):= by
 apply Kd
 · rfl
 · rfl
end v9
namespace Bi
lemma FJ {r: Fin N} (A B: Bi G M r) (hArcs: A.NS=B.NS): A=B:= by
 cases A
 cases B
 cases hArcs
 rfl
lemma HM (E: wF G M H K) (F: wF H K L R)
   {r: Fin N} (S: Bi G M r):(S.Nd E).Nd F=S.Nd (E.comp F):= by
 apply FJ
 change (S.NS.image E.pairMap).image F.pairMap=S.NS.image (E.comp F).pairMap
 rw [image_image]
 rfl
end Bi
namespace Lp
lemma Kd {r: Fin N} (A B: Lp G M r) (hTree: A.tree=B.tree)
   (hActive: A.active=B.active) (hHeld: A.NU=B.NU) (hModified: A.modified=B.modified)
   (hExtended: A.extended=B.extended): A=B:= by
 cases A
 cases B
 cases hTree
 cases hActive
 cases hHeld
 cases hModified
 cases hExtended
 rfl
lemma HM (E: wF G M H K) (F: wF H K L R)
   {r: Fin N} (S: Lp G M r):(S.Nd E).Nd F=S.Nd (E.comp F):= by
 apply Kd
 · exact S.tree.HM E F
 · change (S.active.map (fun A=>A.Nd E)).map (fun A=>A.Nd F)=
     S.active.map (fun A=>A.Nd (E.comp F))
   rw [Option.map_map]
   apply congrArg (fun f=>S.active.map f)
   funext A
   exact A.HM E F
 · rfl
 · rfl
 · rfl
end Lp
end Be
end
noncomputable section
namespace Be
structure y9 (D E: y6) where
 map: wF D.graph D.MG E.graph E.MG
 identity:∀i,E.identity (map.toFun i)=D.identity i
namespace y6
def HA (D E: y6) (hKeys: D.keys⊆E.keys) (i: Fin D.keys.card): Fin E.keys.card:=
 E.enumerate.symm ⟨D.identity i,hKeys (D.Hy i)⟩
lemma mY (D E: y6) (hKeys: D.keys⊆E.keys) (i: Fin D.keys.card):
   E.identity (D.HA E hKeys i)=D.identity i:=
 congrArg Subtype.val (E.enumerate.apply_symm_apply ⟨D.identity i,hKeys (D.Hy i)⟩)
lemma kL (D E: y6) (hKeys: D.keys⊆E.keys):
   Function.Injective (D.HA E hKeys):= by
 intro i j h
 apply D.identity_injective
 rw [←D.mY E hKeys i,←D.mY E hKeys j,h]
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ids: Fin N→ ℕ} {out: Fin N→ Option ℕ}
lemma oF (D: y6) (hi: Function.Injective ids)
   (hAuth: D.Li G ids out): D.JS:= by
 intro a ha b hb hId
 obtain ⟨u,rfl⟩:=hAuth a ha
 obtain ⟨v,rfl⟩:=hAuth b hb
 have hUV: u=v:=hi hId
 rw [hUV]
lemma LL (D E: y6) (hDE: D⊆E): D.keys⊆E.keys:=image_subset_image hDE
lemma Bx (D E: y6) (hi: Function.Injective ids)
   (hD: D.Li G ids out) (hE: E.Li G ids out) (hDE: D⊆E) (hClosed: D.JX)
   (j: ℕ) (hj: j∈D.keys) (k: ℕ) (hMate: E.NW j=some k): k∈E.keys:= by
 obtain ⟨v,hV⟩:=D.Fv hD j hj
 have hOldKey: ids v∈D.keys:=by rw [hV];exact hj
 have hNewKey: ids v∈E.keys:=(D.LL E hDE) hOldKey
 have hOldMate: D.NW j=some k:= by
   rw [←hV,D.Dj hi hD v hOldKey]
   rw [←hV,E.Dj hi hE v hNewKey] at hMate
   exact hMate
 exact D.LL E hDE (hClosed j hj k hOldMate)
lemma iY (D E: y6) (hi: Function.Injective ids)
   (hOut: ReportsMatching G ids out M) (hD: D.Li G ids out) (hE: E.Li G ids out)
   (hClosedD: D.JX) (hClosedE: E.JX) (hKeys: D.keys⊆E.keys):
   Nonempty (y9 D E):= by
 let A:=D.embedding hD hi hOut hClosedD
 let B:=E.embedding hE hi hOut hClosedE
 let f:=D.HA E hKeys
 have hCommute (i: Fin D.keys.card): B.toFun (f i)=A.toFun i:= by
   apply hi
   exact (E.yA hE (f i)).trans
     ((D.mY E hKeys i).trans (D.yA hD i).symm)
 let F: wF D.graph D.MG E.graph E.MG:={
   toFun:=f
   injective:=D.kL E hKeys
   LH:=by
     intro u v
     rw [←B.LH,hCommute,hCommute]
     exact A.LH u v
   HS:=by
     intro u v
     rw [←B.HS,hCommute,hCommute]
     exact A.HS u v
   B7:=by
     intro u w hMatch
     have hGlobal:=(B.HS (f u) w).mpr hMatch
     rw [hCommute] at hGlobal
     obtain ⟨v,hV⟩:=A.B7 u (B.toFun w) hGlobal
     refine ⟨v,B.injective ?_⟩
     exact (hCommute v).trans hV}
 exact ⟨⟨F,D.mY E hKeys⟩⟩
end y6
namespace y9
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ids: Fin N→ ℕ} {out: Fin N→ Option ℕ}
   {D E: y6} (F: y9 D E)
lemma x9 (hi: Function.Injective ids) (hD: D.Li G ids out)
   (hE: E.Li G ids out) (i: Fin D.keys.card):
   E.MQ hE (F.map.toFun i)=D.MQ hD i:= by
 apply hi
 exact (E.yA hE (F.map.toFun i)).trans
   ((F.identity i).trans (D.yA hD i).symm)
lemma DD (hi: Function.Injective ids) (hOut: ReportsMatching G ids out M)
   (hD: D.Li G ids out) (hE: E.Li G ids out)
   (hClosedD: D.JX) (hClosedE: E.JX):
   F.map.comp (E.embedding hE hi hOut hClosedE)=D.embedding hD hi hOut hClosedD:= by
 apply wF.DG
 funext i
 exact F.x9 hi hD hE i
end y9
end Be
end
noncomputable section
namespace Be
variable {N: ℕ}
structure G8 (G M: SimpleGraph (Fin N)) where
 state:(r: Fin N)→ Option (Lp G M r)
 disjoint:∀r s,r≠ s→∀A B,state r= some A→ state s= some B→
   Disjoint A.tree.vertices B.tree.vertices
namespace G8
variable {G M: SimpleGraph (Fin N)} (F: G8 G M)
def Mm (r v: Fin N): Prop:=∃S,F.state r= some S∧ v∈ S.tree.vertices
def Reaches (r: Fin N) (e: Fin N ×Fin N): Prop:=∃S,F.state r= some S∧ S.tree.Reaches e
def Mq (ell: ℕ) (labels: Fin N ×Fin N→ ℕ): Prop:=
 ∀r S,F.state r= some S→ S.Mq ell labels
def roots: Finset (Fin N):= univ.filter (fun r=>(F.state r).isSome)
lemma BE (r s v: Fin N) (hr: F.Mm r v) (hs: F.Mm s v): r= s:= by
 by_contra hne
 obtain ⟨A,hA,hvA⟩:= hr
 obtain ⟨B,hB,hvB⟩:= hs
 exact disjoint_left.mp (F.disjoint r s hne A B hA hB) hvA hvB
lemma AK (r: Fin N) (e: Fin N ×Fin N) (he: F.Reaches r e): F.Mm r e.1∧ F.Mm r e.2:= by
 obtain ⟨S,hS,he⟩:= he
 have hh:= S.tree.yG e he
 exact ⟨⟨S,hS,hh.1⟩,⟨S,hS,hh.2⟩⟩
lemma EF (r s: Fin N) (e: Fin N ×Fin N) (hr: F.Reaches r e) (hs: F.Reaches s e): r= s:=
 F.BE r s e.1 (F.AK r e hr).1 (F.AK s e hs).1
lemma pP (r s: Fin N) (e: Fin N ×Fin N)
   (hr: F.Reaches r e) (hs: F.Reaches s e.swap): r= s:=
 F.BE r s e.2 (F.AK r e hr).2 (F.AK s e.swap hs).1
def LU (f:∀r,Lp G M r→ Lp G M r)
   (hvertices:∀r S,(f r S).tree.vertices= S.tree.vertices): G8 G M where
 state r:=(F.state r).map (f r)
 disjoint:= by
   intro r s hrs A B hA hB
   cases hr: F.state r with
   | none => simp [hr] at hA
   | some R =>
     cases hs: F.state s with
     | none => simp [hs] at hB
     | some S =>
       simp only [hr,Option.map_some,Option.some.injEq] at hA
       simp only [hs,Option.map_some,Option.some.injEq] at hB
       rw [←hA,←hB,hvertices,hvertices]
       exact F.disjoint r s hrs R S hr hs
lemma uO (f:∀r,Lp G M r→ Lp G M r)
   (hvertices:∀r S,(f r S).tree.vertices= S.tree.vertices)
   (ell: ℕ) (labels: Fin N ×Fin N→ ℕ) (hF: F.Mq ell labels)
   (hf:∀r S,S.Mq ell labels→(f r S).Mq ell labels):
   (F.LU f hvertices).Mq ell labels:= by
 intro r S hS
 change (F.state r).map (f r)= some S at hS
 cases hr: F.state r with
 | none => simp [hr] at hS
 | some R =>
   simp only [hr,Option.map_some,Option.some.injEq] at hS
   rw [←hS]
   exact hf r R (hF r R hr)
def initial (G M: SimpleGraph (Fin N)): G8 G M where
 state r:= if h:∀w,¬M.Adj r w then some (Lp.initial G M r h) else none
 disjoint:= by
   intro r s hrs A B hA hB
   split_ifs at hA with hr
   · split_ifs at hB with hs
     · cases Option.some.inj hA
       cases Option.some.inj hB
       change Disjoint ({r} ∪(∅: Finset (Fin N ×Fin N)).biUnion (fun e: Fin N ×Fin N=>{e.1,e.2}))
         ({s} ∪(∅: Finset (Fin N ×Fin N)).biUnion (fun e: Fin N ×Fin N=>{e.1,e.2}))
       simpa using hrs
lemma Ab (G M: SimpleGraph (Fin N)) (ell: ℕ) (labels: Fin N ×Fin N→ ℕ):
   (initial G M).Mq ell labels:= by
 intro r S hS
 change (if h:∀w,¬M.Adj r w then some (Lp.initial G M r h) else none)= some S at hS
 split_ifs at hS with hf
 · cases Option.some.inj hS
   exact Lp.Ab G M r hf ell labels
end G8
end Be
end
noncomputable section
namespace Be.Bi
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {root: Fin N} (S: Bi G M root)
def Dq (C: Finset (Fin N ×Fin N)): Finset (Fin N ×Fin N):=
 C.filter (fun e=>¬M.Adj e.1 e.2∧ e.1∈ S.vertices∧ e.2∈ S.vertices)
def FX (C: Finset (Fin N ×Fin N)) (hC:∀u v,(u,v)∈ C→ G.Adj u v): Bi G M root:=
 S.BI (S.NS ∪S.Dq C) subset_union_left
   (by
     intro u v he
     rcases mem_union.mp he with he|he
     · exact S.valid u v he
     · exact hC u v (mem_filter.mp he).1)
   (by
     intro u v he hm
     rcases mem_union.mp he with he|he
     · exact he
     · exact ((mem_filter.mp he).2.1 hm).elim)
   (by
     intro u v he
     rcases mem_union.mp he with he|he
     · exact S.Ft u v he
     · exact (mem_filter.mp he).2.2)
lemma kK (C: Finset (Fin N ×Fin N)) (hC:∀u v,(u,v)∈ C→ G.Adj u v):
   (S.FX C hC).vertices= S.vertices:= S.gB _ _ _ _ _
lemma i0 (C: Finset (Fin N ×Fin N)) (hC:∀u v,(u,v)∈ C→ G.Adj u v)
   (u v: Fin N) (he:(u,v)∈ C) (hm:¬M.Adj u v) (hu: u∈ S.vertices) (hv: v∈ S.vertices):
   (u,v)∈(S.FX C hC).NS:= mem_union_right _ (mem_filter.mpr ⟨he,hm,hu,hv⟩)
lemma o0 (C: Finset (Fin N ×Fin N)) (hC:∀u v,(u,v)∈ C→ G.Adj u v)
   (hSC: S.NS ⊆C):(S.FX C hC).NS ⊆C:= union_subset hSC (filter_subset _ _)
end Be.Bi
end
noncomputable section
namespace Be.Lp
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {root: Fin N} (S: Lp G M root)
end Be.Lp
namespace Be.G8
variable {N: ℕ} {G M: SimpleGraph (Fin N)} (F: G8 G M)
def qK: Prop:=∀r S,F.state r= some S→ S.tree.qK
end Be.G8
end
noncomputable section
namespace Be
variable {N: ℕ}
structure JT (G: SimpleGraph (Fin N)) (root: Fin N) where
 length: ℕ
 vertex: ℕ→ Fin N
 first: vertex 0= root
 injective:∀i j,i≤ length→ j≤ length→ vertex i= vertex j→ i= j
 Mu:∀i,i< length→ G.Adj (vertex i) (vertex (i+1))
namespace JT
variable {G: SimpleGraph (Fin N)} {root: Fin N} (P: JT G root)
def support: Finset (Fin N):=(range (P.length+1)).image P.vertex
def trivial (G: SimpleGraph (Fin N)) (root: Fin N): JT G root where
 length:= 0
 vertex _:= root
 first:= rfl
 injective:= by intros;omega
 Mu:= by intros;omega
lemma mem_support (i: ℕ) (hi: i≤ P.length): P.vertex i∈ P.support:= mem_image.mpr ⟨i,mem_range.mpr (by omega),rfl⟩
lemma IB: P.support.card= P.length+1:= by
 unfold support
 rw [card_image_of_injOn]
 · exact card_range _
 · intro i hi j hj he
   exact P.injective i j (by have h:=mem_range.mp hi;omega) (by have h:=mem_range.mp hj;omega) he
lemma length_lt: P.length< N:= by
 have hh:= card_le_univ P.support
 rw [P.IB,Fintype.card_fin] at hh
 omega
def He (v: Fin N) (i: ℕ): Fin N:= if i≤ P.length then P.vertex i else v
def extend (v: Fin N) (hG: G.Adj (P.vertex P.length) v) (hv: v∉ P.support): JT G root where
 length:= P.length+1
 vertex:= P.He v
 first:= by rw [He,if_pos (Nat.zero_le _)];exact P.first
 injective:= by
   intro i j hi hj he
   by_cases hi0: i≤ P.length<;> by_cases hj0: j≤ P.length
   · rw [He,if_pos hi0,He,if_pos hj0] at he
     exact P.injective i j hi0 hj0 he
   · rw [He,if_pos hi0,He,if_neg hj0] at he
     exact (hv (he ▸P.mem_support i hi0)).elim
   · rw [He,if_neg hi0,He,if_pos hj0] at he
     exact (hv (he.symm ▸P.mem_support j hj0)).elim
   · omega
 Mu:= by
   intro i hi
   by_cases hi0: i< P.length
   · rw [He,if_pos (by omega: i≤ P.length),He,if_pos (by omega: i+1≤ P.length)]
     exact P.Mu i hi0
   · have hi': i= P.length:= by omega
     subst i
     rw [He,if_pos le_rfl,He,if_neg (by omega:¬P.length+1≤ P.length)]
     exact hG
lemma D9 (G: SimpleGraph (Fin N)) (root: Fin N):
   ∃P: JT G root,∀Q: JT G root,Q.length≤ P.length:= by
 let F:=(range N).filter (fun n=>∃P: JT G root,P.length= n)
 have hF: F.Nonempty:= by
   refine ⟨0,mem_filter.mpr ⟨mem_range.mpr (by have hh:=root.isLt;omega),trivial G root,rfl⟩⟩
 let n:= F.max' hF
 have hn:= max'_mem F hF
 obtain ⟨P,hPn⟩:=(mem_filter.mp hn).2
 refine ⟨P,?_⟩
 intro Q
 rw [hPn]
 exact le_max' F Q.length (mem_filter.mpr ⟨mem_range.mpr Q.length_lt,Q,rfl⟩)
lemma uI (hmax:∀Q: JT G root,Q.length≤ P.length)
   (v: Fin N) (hv: G.Adj (P.vertex P.length) v): v∈ P.support:= by
 by_contra hnot
 have hh:= hmax (P.extend v hv hnot)
 change P.length+1≤ P.length at hh
 omega
end JT
lemma tW {G: SimpleGraph (Fin N)} (v a b: Fin N) (ha: G.Adj v a) (hb: G.Adj v b)
   (hab: a≠ b) (hdeg: G.degree v≤ 2) (w: Fin N) (hw: G.Adj v w): w= a∨ w= b:= by
 have hsub:({a,b}: Finset (Fin N)) ⊆G.neighborFinset v:= by
   intro u hu
   rcases mem_insert.mp hu with hu|hu
   · rw [hu]
     exact (G.mem_neighborFinset v a).mpr ha
   · rw [mem_singleton.mp hu]
     exact (G.mem_neighborFinset v b).mpr hb
 have hcard:({a,b}: Finset (Fin N)).card= 2:= by simp [hab]
 have heq:({a,b}: Finset (Fin N))= G.neighborFinset v:= eq_of_subset_of_card_le hsub (by rw [hcard,G.card_neighborFinset_eq_degree];exact hdeg)
 have hh: w∈({a,b}: Finset (Fin N)):= by rw [heq];exact (G.mem_neighborFinset v w).mpr hw
 simpa only [mem_insert,mem_singleton] using hh
lemma tV {G: SimpleGraph (Fin N)} (v a: Fin N) (ha: G.Adj v a)
   (hdeg: G.degree v≤ 1) (w: Fin N) (hw: G.Adj v w): w= a:= by
 have hcard:(G.neighborFinset v).card≤ 1:= by rwa [G.card_neighborFinset_eq_degree]
 exact card_le_one.mp hcard w ((G.mem_neighborFinset v w).mpr hw) a ((G.mem_neighborFinset v a).mpr ha)
namespace JT
variable {G: SimpleGraph (Fin N)} {root: Fin N} (P: JT G root)
lemma kV (hmax:∀Q: JT G root,Q.length≤ P.length)
   (hdeg:∀v,G.degree v≤ 2) (hroot: G.degree root≤ 1)
   (u v: Fin N) (hu: u∈ P.support) (huv: G.Adj u v): v∈ P.support:= by
 obtain ⟨i,hi,rfl⟩:= mem_image.mp hu
 have hi': i≤ P.length:= by have h:=mem_range.mp hi;omega
 by_cases hiend: i= P.length
 · subst i
   exact P.uI hmax v huv
 · by_cases hi0: i= 0
   · subst i
     have hlen: 0< P.length:= by omega
     have hfirst:= P.Mu 0 hlen
     rw [P.first] at huv hfirst
     have hv:= tV root (P.vertex 1) hfirst hroot v huv
     rw [hv]
     exact P.mem_support 1 (by omega)
   · have hleft: G.Adj (P.vertex i) (P.vertex (i-1)):= by
       have h:= P.Mu (i-1) (by omega)
       rw [show i-1+1= i by omega] at h
       exact h.symm
     have hright:= P.Mu i (by omega)
     have hne: P.vertex (i-1)≠ P.vertex (i+1):= by
       intro he
       have hh:= P.injective (i-1) (i+1) (by omega) (by omega) he
       omega
     rcases tW (P.vertex i) (P.vertex (i-1)) (P.vertex (i+1)) hleft hright hne (hdeg _) v huv with hv|hv
     · rw [hv];exact P.mem_support _ (by omega)
     · rw [hv];exact P.mem_support _ (by omega)
end JT
end Be
end
noncomputable section
namespace qJ
variable {N: ℕ}
lemma gQ (G M: SimpleGraph (Fin N)) (hM: Matching G M): matchingSize M≤ optimum G:= by
 let lift: M.edgeSet→ G.edgeSet:= fun e=>⟨e.val,SimpleGraph.edgeSet_mono hM.1 e.property⟩
 let E: Finset G.edgeSet:= univ.image lift
 have hi: Function.Injective lift:= fun e f h=> Subtype.ext (congrArg (fun e: G.edgeSet=> e.val) h)
 have hE: SemiStreamMWM.IsMatching G E:= by
   intro e he f hf hne v hve hvf
   obtain ⟨a,ha,rfl⟩:= mem_image.mp he
   obtain ⟨b,hb,rfl⟩:= mem_image.mp hf
   exact hM.2 a (mem_univ _) b (mem_univ _) (fun h=> hne (congrArg lift h)) v hve hvf
 have hc: E.card= matchingSize M:= by
   unfold E
   rw [card_image_of_injective _ hi,card_univ,M.card_edgeSet]
   rfl
 have hle: E.card≤ optimum G:=
   le_sup (f:=Finset.card) (mem_filter.mpr ⟨mem_univ _,hE⟩)
 rwa [hc] at hle
lemma F9 (G: SimpleGraph (Fin N)):∃M: SimpleGraph (Fin N),Matching G M∧ matchingSize M= optimum G:= by
 obtain ⟨E,hE,hcard⟩:= wA.Al G
 refine ⟨wA.LC G E,wA.tX G E hE,?_⟩
 rw [wA.DB,hcard]
end qJ
end
noncomputable section
namespace Be
variable {N: ℕ}
def Dy (G: SimpleGraph (Fin N)) (D: Finset (Fin N)): SimpleGraph (Fin N) where
 Adj u v:= G.Adj u v∧ u∉ D∧ v∉ D
 symm:=⟨by rintro u v ⟨h,hu,hv⟩;exact ⟨h.symm,hv,hu⟩⟩
 loopless:=⟨by intro v h;exact h.1.ne rfl⟩
end Be
end
noncomputable section
namespace Be
variable {N: ℕ}
def B5 (M: SimpleGraph (Fin N)): Finset (Fin N):= M.edgeFinset.biUnion Sym2.toFinset
lemma rW (M: SimpleGraph (Fin N)) (v: Fin N): v∈ B5 M↔∃w,M.Adj v w:= by
 constructor
 · intro hv
   obtain ⟨e,he,hv⟩:= mem_biUnion.mp hv
   obtain ⟨w,hw⟩:= Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp hv)
   refine ⟨w,M.mem_edgeSet.mp ?_⟩
   rw [←hw]
   exact M.mem_edgeFinset.mp he
 · rintro ⟨w,hw⟩
   exact mem_biUnion.mpr ⟨s(v,w),M.mem_edgeFinset.mpr (M.mem_edgeSet.mpr hw),Sym2.mem_toFinset.mpr (Sym2.mem_mk_left _ _)⟩
lemma pC (G M: SimpleGraph (Fin N)) (hM: Matching G M):(B5 M).card= 2*matchingSize M:= by
 have hd: Set.Pairwise (M.edgeFinset: Set (Sym2 (Fin N))) (fun e f=> Disjoint e.toFinset f.toFinset):= by
   intro e he f hf hne
   apply disjoint_left.mpr
   intro v hve hvf
   exact hM.2 ⟨e,M.mem_edgeFinset.mp he⟩ (mem_univ _) ⟨f,M.mem_edgeFinset.mp hf⟩ (mem_univ _)
     (fun h=> hne (congrArg Subtype.val h)) v (Sym2.mem_toFinset.mp hve) (Sym2.mem_toFinset.mp hvf)
 unfold B5
 rw [card_biUnion hd]
 calc
   _=∑_∈ M.edgeFinset,(2:ℕ):= sum_congr rfl (fun e he=> Sym2.card_toFinset_of_not_isDiag e (M.not_isDiag_of_mem_edgeFinset he))
   _= _:= by simp [matchingSize,mul_comm]
lemma kX (G M: SimpleGraph (Fin N)) (hM: Matching G M) (v: Fin N): M.degree v≤ 1:= by
 rw [←M.card_neighborFinset_eq_degree]
 apply card_le_one.mpr
 intro a ha b hb
 exact qJ.gP G M hM v a b
   ((M.mem_neighborFinset v a).mp ha) ((M.mem_neighborFinset v b).mp hb)
def comparison (M K: SimpleGraph (Fin N)): SimpleGraph (Fin N):=(M \K) ⊔(K \M)
lemma FB (G M K: SimpleGraph (Fin N)) (hM: M≤ G) (hK: K≤ G): comparison M K≤ G:= by
 intro u v h
 exact h.elim (fun h=> hM h.1) (fun h=> hK h.1)
lemma wQ (G M K: SimpleGraph (Fin N)) (hM: Matching G M) (hK: Matching G K) (v: Fin N):
   (comparison M K).degree v≤ 2:= by
 have hsub:(comparison M K).neighborFinset v ⊆M.neighborFinset v ∪K.neighborFinset v:= by
   intro w hw
   have h:=((comparison M K).mem_neighborFinset v w).mp hw
   exact h.elim (fun h=> mem_union_left _ ((M.mem_neighborFinset v w).mpr h.1))
     (fun h=> mem_union_right _ ((K.mem_neighborFinset v w).mpr h.1))
 have hh:=(card_le_card hsub).trans (card_union_le _ _)
 rw [SimpleGraph.card_neighborFinset_eq_degree,SimpleGraph.card_neighborFinset_eq_degree,SimpleGraph.card_neighborFinset_eq_degree] at hh
 have hm:= kX G M hM v
 have hk:= kX G K hK v
 omega
lemma j7 (G M K: SimpleGraph (Fin N)) (hK: Matching G K) (v: Fin N)
   (hfree:∀w,¬M.Adj v w):(comparison M K).degree v≤ 1:= by
 have hsub:(comparison M K).neighborFinset v ⊆K.neighborFinset v:= by
   intro w hw
   have h:=((comparison M K).mem_neighborFinset v w).mp hw
   rcases h with h|h
   · exact (hfree w h.1).elim
   · exact (K.mem_neighborFinset v w).mpr h.1
 have hh:= card_le_card hsub
 rw [SimpleGraph.card_neighborFinset_eq_degree,SimpleGraph.card_neighborFinset_eq_degree] at hh
 exact hh.trans (kX G K hK v)
lemma iN (G M K: SimpleGraph (Fin N)) (hM: Matching G M) (hK: Matching G K)
   (hsize: matchingSize M< matchingSize K):∃r w,(∀v,¬M.Adj r v)∧ K.Adj r w:= by
 have hnot:¬B5 K ⊆B5 M:= by
   intro hsub
   have hh:= card_le_card hsub
   rw [pC G K hK,pC G M hM] at hh
   omega
 obtain ⟨r,hrK,hrM⟩:= not_subset.mp hnot
 obtain ⟨w,hw⟩:=(rW K r).mp hrK
 refine ⟨r,w,?_,hw⟩
 intro v hv
 exact hrM ((rW M r).mpr ⟨v,hv⟩)
end Be
end
noncomputable section
namespace Be.JT
variable {N: ℕ} {G: SimpleGraph (Fin N)} {root: Fin N} (P: JT G root)
lemma i2 (hdeg:∀v,G.degree v≤ 2) (hroot: G.degree root≤ 1)
   (i j: ℕ) (hi: i< P.length) (hj: j≤ P.length) (hG: G.Adj (P.vertex i) (P.vertex j)):
   j+1= i∨ i+1= j:= by
 by_cases hi0: i= 0
 · subst i
   have hfirst:= P.Mu 0 hi
   have hG':= hG
   rw [P.first] at hfirst hG'
   have he:= tV root (P.vertex 1) hfirst hroot (P.vertex j) hG'
   have hj': j= 1:= P.injective j 1 hj (by omega) he
   exact Or.inr hj'.symm
 · have hprev: G.Adj (P.vertex i) (P.vertex (i-1)):= by
     have h:= P.Mu (i-1) (by omega)
     rw [show i-1+1= i by omega] at h
     exact h.symm
   have hnext:= P.Mu i hi
   have hne: P.vertex (i-1)≠ P.vertex (i+1):= by
     intro he
     have hh:= P.injective (i-1) (i+1) (by omega) (by omega) he
     omega
   rcases tW (P.vertex i) (P.vertex (i-1)) (P.vertex (i+1)) hprev hnext hne (hdeg _) (P.vertex j) hG with he|he
   · have hj':= P.injective j (i-1) hj (by omega) he
     exact Or.inl (by omega)
   · exact Or.inr (P.injective j (i+1) hj (by omega) he).symm
lemma Aa (hdeg:∀v,G.degree v≤ 2) (hroot: G.degree root≤ 1)
   (i j: ℕ) (hi: i≤ P.length) (hj: j≤ P.length) (hG: G.Adj (P.vertex i) (P.vertex j)):
   j+1= i∨ i+1= j:= by
 by_cases hi': i< P.length
 · exact P.i2 hdeg hroot i j hi' hj hG
 · have hj': j< P.length:= by
     by_contra hnot
     have he: j= i:= by omega
     rw [he] at hG
     exact hG.ne rfl
   exact (P.i2 hdeg hroot j i hj' hi hG.symm).symm
lemma o8 (hmax:∀Q: JT G root,Q.length≤ P.length)
   (hdeg:∀v,G.degree v≤ 2) (hroot: G.degree root≤ 1)
   (v: Fin N) (hv: G.Adj (P.vertex P.length) v): v= P.vertex (P.length-1):= by
 obtain ⟨i,hi,he⟩:= mem_image.mp (P.uI hmax v hv)
 have hi': i≤ P.length:= by have h:=mem_range.mp hi;omega
 have hh:= P.Aa hdeg hroot P.length i le_rfl hi' (he.symm ▸hv)
 have he': i= P.length-1:= by omega
 rw [←he,he']
lemma uJ (hmax:∀Q: JT G root,Q.length≤ P.length)
   (hdeg:∀v,G.degree v≤ 2) (hroot: G.degree root≤ 1): G.degree (P.vertex P.length)≤ 1:= by
 rw [←G.card_neighborFinset_eq_degree]
 apply card_le_one.mpr
 intro v hv w hw
 exact (P.o8 hmax hdeg hroot v ((G.mem_neighborFinset _ _).mp hv)).trans
   (P.o8 hmax hdeg hroot w ((G.mem_neighborFinset _ _).mp hw)).symm
end Be.JT
end
noncomputable section
namespace Be
variable {N: ℕ} {G M K: SimpleGraph (Fin N)} {root: Fin N}
lemma j9 (hM: Matching G M) (hK: Matching G K) (v w: Fin N)
   (hdeg:(comparison M K).degree v≤ 1) (hMedge: M.Adj v w) (hKnot:¬K.Adj v w):∀u,¬K.Adj v u:= by
 intro u hKu
 have hMunot:¬M.Adj v u:= by
   intro hMu
   have he:= qJ.gP G M hM v w u hMedge hMu
   exact hKnot (he.symm ▸hKu)
 have hcW:(comparison M K).Adj v w:= Or.inl ⟨hMedge,hKnot⟩
 have hcU:(comparison M K).Adj v u:= Or.inr ⟨hKu,hMunot⟩
 have he:= tV v w hcW hdeg u hcU
 exact hKnot (he ▸hKu)
namespace JT
variable (P: JT (comparison M K) root)
lemma dU (hM: Matching G M) (hK: Matching G K) (i: ℕ) (hi: i+1< P.length):
   M.Adj (P.vertex (i+1)) (P.vertex (i+2))↔¬M.Adj (P.vertex i) (P.vertex (i+1)):= by
 have ha:= P.Mu i (by omega)
 have hb:= P.Mu (i+1) hi
 have hneq: P.vertex i≠ P.vertex (i+2):= by
   intro he
   have hh:= P.injective i (i+2) (by omega) (by omega) he
   omega
 have hnM:¬(M.Adj (P.vertex i) (P.vertex (i+1))∧ M.Adj (P.vertex (i+1)) (P.vertex (i+2))):= by
   rintro ⟨h1,h2⟩
   exact hneq (qJ.gP G M hM _ _ _ h1.symm h2)
 have hnK:¬(K.Adj (P.vertex i) (P.vertex (i+1))∧ K.Adj (P.vertex (i+1)) (P.vertex (i+2))):= by
   rintro ⟨h1,h2⟩
   exact hneq (qJ.gP G K hK _ _ _ h1.symm h2)
 change (M.Adj (P.vertex i) (P.vertex (i+1))∧¬K.Adj (P.vertex i) (P.vertex (i+1)))∨
   (K.Adj (P.vertex i) (P.vertex (i+1))∧¬M.Adj (P.vertex i) (P.vertex (i+1))) at ha
 change (M.Adj (P.vertex (i+1)) (P.vertex (i+2))∧¬K.Adj (P.vertex (i+1)) (P.vertex (i+2)))∨
   (K.Adj (P.vertex (i+1)) (P.vertex (i+2))∧¬M.Adj (P.vertex (i+1)) (P.vertex (i+2))) at hb
 tauto
lemma q1 (hM: Matching G M) (hK: Matching G K)
   (hfree:∀w,¬M.Adj root w) (i: ℕ) (hi: i< P.length):
   M.Adj (P.vertex i) (P.vertex (i+1))↔ Odd i:= by
 induction i with
 | zero =>
   have hh:¬M.Adj (P.vertex 0) (P.vertex 1):= by rw [P.first];exact hfree _
   constructor
   · exact fun h=>(hh h).elim
   · rintro ⟨j,hj⟩;omega
 | succ i ih =>
   have hh:= P.dU hM hK i hi
   have hp:¬Odd i↔ Odd (i+1):= by rw [Nat.odd_iff,Nat.odd_iff];omega
   exact hh.trans ((ih (by omega)).not.trans hp)
lemma qZ (hM: Matching G M) (hK: Matching G K)
   (hfree:∀w,¬M.Adj root w) (i: ℕ) (hi: i< P.length):
   K.Adj (P.vertex i) (P.vertex (i+1))↔ Even i:= by
 have hc:= P.Mu i hi
 have hMK: K.Adj (P.vertex i) (P.vertex (i+1))↔¬M.Adj (P.vertex i) (P.vertex (i+1)):= by
   change (M.Adj (P.vertex i) (P.vertex (i+1))∧¬K.Adj (P.vertex i) (P.vertex (i+1)))∨
     (K.Adj (P.vertex i) (P.vertex (i+1))∧¬M.Adj (P.vertex i) (P.vertex (i+1))) at hc
   tauto
 have hp:¬Odd i↔ Even i:= by rw [Nat.odd_iff,Nat.even_iff];omega
 exact hMK.trans ((P.q1 hM hK hfree i hi).not.trans hp)
end JT
end Be
end
noncomputable section
namespace Be
variable {N: ℕ}
def FW (M: SimpleGraph (Fin N)) (D: Finset (Fin N)): Finset (Sym2 (Fin N)):=
 M.edgeFinset.filter (fun e=>∃v∈ D,v∈ e)
lemma FG (M: SimpleGraph (Fin N)) (D: Finset (Fin N)):
   (Dy M D).edgeFinset= M.edgeFinset \FW M D:= by
 ext e
 obtain ⟨⟨u,v⟩,rfl⟩:= e.exists_rep
 rw [(Dy M D).mem_edgeFinset,mem_sdiff]
 simp only [FW,mem_filter,M.mem_edgeFinset]
 change (M.Adj u v∧ u∉ D∧ v∉ D)↔ M.Adj u v∧¬(M.Adj u v∧∃w∈ D,w∈ s(u,v))
 constructor
 · rintro ⟨huv,hu,hv⟩
   refine ⟨huv,?_⟩
   rintro ⟨_,w,hwD,hw⟩
   rcases Sym2.mem_iff.mp hw with hw|hw
   · exact hu (hw ▸hwD)
   · exact hv (hw ▸hwD)
 · rintro ⟨huv,hnot⟩
   refine ⟨huv,?_,?_⟩
   · intro hu
     exact hnot ⟨huv,u,hu,Sym2.mem_mk_left _ _⟩
   · intro hv
     exact hnot ⟨huv,v,hv,Sym2.mem_mk_right _ _⟩
lemma Hq (M: SimpleGraph (Fin N)) (D: Finset (Fin N)):
   matchingSize (Dy M D)+(FW M D).card= matchingSize M:= by
 unfold matchingSize
 rw [FG]
 exact card_sdiff_add_card_eq_card (filter_subset _ _)
namespace JT
variable {G: SimpleGraph (Fin N)} {root: Fin N} (P: JT G root)
def ML: Finset (Sym2 (Fin N)):=
 (range (P.length/2)).image (fun i=> s(P.vertex (2*i+1),P.vertex (2*i+2)))
def LE: Finset (Sym2 (Fin N)):=
 (range ((P.length+1)/2)).image (fun i=> s(P.vertex (2*i),P.vertex (2*i+1)))
lemma DC (a b: ℕ) (ha: a< P.length) (hb: b< P.length)
   (he: s(P.vertex a,P.vertex (a+1))= s(P.vertex b,P.vertex (b+1))): a= b:= by
 rcases Sym2.eq_iff.mp he with he|he
 · exact P.injective a b (by omega) (by omega) he.1
 · have h1:= P.injective a (b+1) (by omega) (by omega) he.1
   have h2:= P.injective (a+1) b (by omega) (by omega) he.2
   omega
lemma Gl: P.ML.card= P.length/2:= by
 unfold ML
 rw [card_image_of_injOn]
 · exact card_range _
 · intro i hi j hj he
   have hh:= P.DC (2*i+1) (2*j+1) (by have h:=mem_range.mp hi;omega) (by have h:=mem_range.mp hj;omega) he
   omega
lemma DJ: P.LE.card=(P.length+1)/2:= by
 unfold LE
 rw [card_image_of_injOn]
 · exact card_range _
 · intro i hi j hj he
   have hh:= P.DC (2*i) (2*j) (by have h:=mem_range.mp hi;omega) (by have h:=mem_range.mp hj;omega) he
   omega
lemma eB (hlen: 0< P.length) (v: Fin N) (hv: v∈ P.support):
   ∃w,G.Adj v w:= by
 obtain ⟨i,hi,rfl⟩:= mem_image.mp hv
 have hi': i≤ P.length:= by have h:=mem_range.mp hi;omega
 by_cases hiend: i= P.length
 · refine ⟨P.vertex (i-1),?_⟩
   have hh:= P.Mu (i-1) (by omega)
   rw [show i-1+1= i by omega] at hh
   exact hh.symm
 · exact ⟨P.vertex (i+1),P.Mu i (by omega)⟩
end JT
end Be
end
noncomputable section
namespace Be.JT
variable {N: ℕ} {G: SimpleGraph (Fin N)} {root: Fin N} (P: JT G root)
lemma B0 (hmax:∀Q: JT G root,Q.length≤ P.length)
   (hdeg:∀v,G.degree v≤ 2) (hroot: G.degree root≤ 1)
   (R: SimpleGraph (Fin N)) (hLocal:∀u,u∈ P.support→∀v,R.Adj u v→ G.Adj u v)
   (e: Sym2 (Fin N)) (he: e∈ FW R P.support):
   ∃i,i< P.length∧ e= s(P.vertex i,P.vertex (i+1))∧ R.Adj (P.vertex i) (P.vertex (i+1)):= by
 obtain ⟨he,v,hv,hve⟩:= mem_filter.mp he
 obtain ⟨w,hew⟩:= Sym2.mem_iff_exists.mp hve
 have hvw: R.Adj v w:= R.mem_edgeSet.mp (by rw [←hew];exact R.mem_edgeFinset.mp he)
 have hG:= hLocal v hv w hvw
 have hw:= P.kV hmax hdeg hroot v w hv hG
 obtain ⟨a,ha,hav⟩:= mem_image.mp hv
 obtain ⟨b,hb,hbw⟩:= mem_image.mp hw
 have ha': a≤ P.length:= by have hh:=mem_range.mp ha;omega
 have hb': b≤ P.length:= by have hh:=mem_range.mp hb;omega
 have hab: G.Adj (P.vertex a) (P.vertex b):= by rwa [hav,hbw]
 rcases P.Aa hdeg hroot a b ha' hb' hab with hab|hab
 · have heb: e= s(P.vertex b,P.vertex (b+1)):= by
     rw [hew,←hav,←hbw,hab]
     exact Sym2.eq_swap
   refine ⟨b,by omega,heb,?_⟩
   exact R.mem_edgeSet.mp (by rw [←heb];exact R.mem_edgeFinset.mp he)
 · have hea: e= s(P.vertex a,P.vertex (a+1)):= by rw [hew,←hav,←hbw,hab]
   refine ⟨a,by omega,hea,?_⟩
   exact R.mem_edgeSet.mp (by rw [←hea];exact R.mem_edgeFinset.mp he)
lemma oZ (hmax:∀Q: JT G root,Q.length≤ P.length)
   (hdeg:∀v,G.degree v≤ 2) (hroot: G.degree root≤ 1)
   (R: SimpleGraph (Fin N)) (hLocal:∀u,u∈ P.support→∀v,R.Adj u v→ G.Adj u v)
   (hpar:∀i,i< P.length→(R.Adj (P.vertex i) (P.vertex (i+1))↔ Odd i)):
   FW R P.support= P.ML:= by
 ext e
 constructor
 · intro he
   obtain ⟨i,hi,heq,hR⟩:= P.B0 hmax hdeg hroot R hLocal e he
   obtain ⟨j,hj⟩:=(hpar i hi).mp hR
   have hij: i= 2*j+1:= by omega
   refine mem_image.mpr ⟨j,mem_range.mpr (by omega),?_⟩
   rw [heq,hij]
 · intro he
   obtain ⟨i,hi,rfl⟩:= mem_image.mp he
   have hi':= mem_range.mp hi
   have hR: R.Adj (P.vertex (2*i+1)) (P.vertex (2*i+2)):=
     (hpar (2*i+1) (by omega)).mpr ⟨i,by omega⟩
   refine mem_filter.mpr ⟨R.mem_edgeFinset.mpr (R.mem_edgeSet.mpr hR),P.vertex (2*i+1),P.mem_support _ (by omega),Sym2.mem_mk_left _ _⟩
lemma mW (hmax:∀Q: JT G root,Q.length≤ P.length)
   (hdeg:∀v,G.degree v≤ 2) (hroot: G.degree root≤ 1)
   (R: SimpleGraph (Fin N)) (hLocal:∀u,u∈ P.support→∀v,R.Adj u v→ G.Adj u v)
   (hpar:∀i,i< P.length→(R.Adj (P.vertex i) (P.vertex (i+1))↔ Even i)):
   FW R P.support= P.LE:= by
 ext e
 constructor
 · intro he
   obtain ⟨i,hi,heq,hR⟩:= P.B0 hmax hdeg hroot R hLocal e he
   obtain ⟨j,hj⟩:=(hpar i hi).mp hR
   have hij: i= 2*j:= by omega
   refine mem_image.mpr ⟨j,mem_range.mpr (by omega),?_⟩
   rw [heq,hij]
 · intro he
   obtain ⟨i,hi,rfl⟩:= mem_image.mp he
   have hi':= mem_range.mp hi
   have hR:=(hpar (2*i) (by omega)).mpr (show Even (2*i) from ⟨i,by omega⟩)
   exact mem_filter.mpr ⟨R.mem_edgeFinset.mpr (R.mem_edgeSet.mpr hR),P.vertex (2*i),P.mem_support _ (by omega),Sym2.mem_mk_left _ _⟩
end Be.JT
end
noncomputable section
namespace Be
variable {N: ℕ} {G M K: SimpleGraph (Fin N)} {root: Fin N}
lemma Bz (M K: SimpleGraph (Fin N)): comparison M K= comparison K M:= sup_comm _ _
lemma dT (hM: Matching G M) (hK: Matching G K) (v u: Fin N)
   (hMu: M.Adj v u) (hKu: K.Adj v u):∀w,¬(comparison M K).Adj v w:= by
 intro w hw
 rcases hw with hw|hw
 · have he:= qJ.gP G M hM v u w hMu hw.1
   exact hw.2 (he ▸hKu)
 · have he:= qJ.gP G K hK v u w hKu hw.1
   exact hw.2 (he ▸hMu)
lemma q3 (hM: Matching G M) (hK: Matching G K) (v u: Fin N)
   (hMu: M.Adj v u) (hactive:∃w,(comparison M K).Adj v w):(comparison M K).Adj v u:= by
 refine Or.inl ⟨hMu,?_⟩
 intro hKu
 obtain ⟨w,hw⟩:= hactive
 exact dT hM hK v u hMu hKu w hw
lemma q2 (hM: Matching G M) (hK: Matching G K) (v u: Fin N)
   (hKu: K.Adj v u) (hactive:∃w,(comparison M K).Adj v w):(comparison M K).Adj v u:= by
 refine Or.inr ⟨hKu,?_⟩
 intro hMu
 obtain ⟨w,hw⟩:= hactive
 exact dT hM hK v u hMu hKu w hw
lemma j8 (hM: Matching G M) (hK: Matching G K) (v w: Fin N)
   (hdeg:(comparison M K).degree v≤ 1) (hKedge: K.Adj v w) (hMnot:¬M.Adj v w):∀u,¬M.Adj v u:= by
 apply j9 hK hM v w
 · rwa [Bz K M]
 · exact hKedge
 · exact hMnot
namespace JT
variable (P: JT (comparison M K) root)
   (hmax:∀Q: JT (comparison M K) root,Q.length≤ P.length)
   (hM: Matching G M) (hK: Matching G K) (hfree:∀w,¬M.Adj root w)
include hmax hfree in
lemma mH (w: Fin N) (hw: K.Adj root w): 0< P.length:= by
 let Q:= trivial (comparison M K) root
 have hcomp:(comparison M K).Adj root w:= Or.inr ⟨hw,hfree w⟩
 have hfresh: w∉ Q.support:= by simp [Q,trivial,support,hw.ne.symm]
 have hh:= hmax (Q.extend w hcomp hfresh)
 change 0+1≤ P.length at hh
 omega
include hmax hM hK hfree in
lemma q0 (hlen: 0< P.length):
   ∀u,u∈ P.support→∀v,M.Adj u v→ v∈ P.support:= by
 intro u hu v huv
 exact P.kV hmax (wQ G M K hM hK)
   (j7 G M K hK root hfree) u v hu
   (q3 hM hK u v huv (P.eB hlen u hu))
include hmax hM hK hfree in
lemma oT (hlen: 0< P.length):
   matchingSize (Dy M P.support)+P.length/2= matchingSize M:= by
 have hLocal:∀u,u∈ P.support→∀v,M.Adj u v→(comparison M K).Adj u v:= by
   intro u hu v huv
   exact q3 hM hK u v huv (P.eB hlen u hu)
 have hh:= Hq M P.support
 rw [P.oZ hmax (wQ G M K hM hK) (j7 G M K hK root hfree) M hLocal
   (P.q1 hM hK hfree),P.Gl] at hh
 exact hh
include hmax hM hK hfree in
lemma oS (hlen: 0< P.length):
   matchingSize (Dy K P.support)+(P.length+1)/2= matchingSize K:= by
 have hLocal:∀u,u∈ P.support→∀v,K.Adj u v→(comparison M K).Adj u v:= by
   intro u hu v huv
   exact q2 hM hK u v huv (P.eB hlen u hu)
 have hh:= Hq K P.support
 rw [P.mW hmax (wQ G M K hM hK) (j7 G M K hK root hfree) K hLocal
   (P.qZ hM hK hfree),P.DJ] at hh
 exact hh
include hmax hM hK hfree in
lemma iM (hodd: Odd P.length):∀w,¬M.Adj (P.vertex P.length) w:= by
 have hlen: 0< P.length:= by obtain ⟨k,hk⟩:= hodd;omega
 have hlast:= P.qZ hM hK hfree (P.length-1) (by omega)
 have hKlast: K.Adj (P.vertex (P.length-1)) (P.vertex P.length):= by
   have hp: Even (P.length-1):= by rw [Nat.even_iff];rw [Nat.odd_iff] at hodd;omega
   have hh:= hlast.mpr hp
   rwa [show P.length-1+1= P.length by omega] at hh
 have hMlast:¬M.Adj (P.vertex P.length) (P.vertex (P.length-1)):= by
   intro hm
   have hh:=(P.q1 hM hK hfree (P.length-1) (by omega)).mp (by
     rw [show P.length-1+1= P.length by omega];exact hm.symm)
   rw [Nat.odd_iff] at hh hodd
   omega
 exact j8 hM hK _ _
   (P.uJ hmax (wQ G M K hM hK) (j7 G M K hK root hfree)) hKlast.symm hMlast
include hmax hM hK hfree in
def wP (hodd: Odd P.length): C3 G M where
 length:= P.length/2
 vertex:= P.vertex
 injective:= by
   intro i j hi hj he
   have hlen: P.length= 2*(P.length/2)+1:= by rw [Nat.odd_iff] at hodd;omega
   exact P.injective i j (by omega) (by omega) he
 Mu:= by
   intro i hi
   have hlen: P.length= 2*(P.length/2)+1:= by rw [Nat.odd_iff] at hodd;omega
   exact FB G M K hM.1 hK.1 (P.Mu i (by omega))
 MG:= by
   intro i hi
   have hlen: P.length= 2*(P.length/2)+1:= by rw [Nat.odd_iff] at hodd;omega
   exact P.q1 hM hK hfree i (by omega)
 Ki:= by intro w;rw [P.first];exact hfree w
 LP:= by
   have hlen: P.length= 2*(P.length/2)+1:= by rw [Nat.odd_iff] at hodd;omega
   rw [←hlen]
   exact P.iM hmax hM hK hfree hodd
include hmax hM hK hfree in
lemma eW (hodd: Odd P.length):
   (P.wP hmax hM hK hfree hodd).support= P.support:= by
 have hlen: P.length= 2*(P.length/2)+1:= by rw [Nat.odd_iff] at hodd;omega
 change (range (2*(P.length/2)+2)).image P.vertex=(range (P.length+1)).image P.vertex
 congr 2<;> omega
end JT
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {I: Type}
def Ld (G: SimpleGraph (Fin N)) (S: Finset I) (H: I→ SimpleGraph (Fin N)): SimpleGraph (Fin N):=
 zD.GB G (S.biUnion (fun i=>(H i).edgeFinset))
lemma E1 (G: SimpleGraph (Fin N)) (S: Finset I) (H: I→ SimpleGraph (Fin N))
   (hHG:∀i∈ S,H i≤ G) (u v: Fin N):
   (Ld G S H).Adj u v↔∃i∈ S,(H i).Adj u v:= by
 constructor
 · rintro ⟨_,he⟩
   obtain ⟨i,hi,he⟩:= mem_biUnion.mp he
   exact ⟨i,hi,(H i).mem_edgeSet.mp ((H i).mem_edgeFinset.mp he)⟩
 · rintro ⟨i,hi,he⟩
   exact ⟨hHG i hi he,mem_biUnion.mpr ⟨i,hi,(H i).mem_edgeFinset.mpr ((H i).mem_edgeSet.mpr he)⟩⟩
lemma A5 (G: SimpleGraph (Fin N)) (S: Finset I) (H: I→ SimpleGraph (Fin N))
   (hHG:∀i∈ S,H i≤ G):
   (Ld G S H).edgeFinset= S.biUnion (fun i=>(H i).edgeFinset):= by
 apply zD.g4
 intro e he
 obtain ⟨i,hi,he⟩:= mem_biUnion.mp he
 exact SimpleGraph.edgeFinset_mono (hHG i hi) he
lemma CW (G: SimpleGraph (Fin N)) (S: Finset I) (H: I→ SimpleGraph (Fin N))
   (hHG:∀i∈ S,H i≤ G)
   (hd: Set.Pairwise (S:Set I) (fun i j=> Disjoint (H i).edgeFinset (H j).edgeFinset)):
   matchingSize (Ld G S H)=∑i∈ S,matchingSize (H i):= by
 unfold matchingSize
 rw [A5 G S H hHG,card_biUnion]
 exact hd
lemma s3 (G: SimpleGraph (Fin N)) (S: Finset I) (H: I→ SimpleGraph (Fin N))
   (hM:∀i∈ S,Matching G (H i))
   (hdis:∀i∈ S,∀j∈ S,i≠ j→∀u v w,(H i).Adj u v→(H j).Adj u w→ False):
   Matching G (Ld G S H):= by
 have hHG:∀i∈ S,H i≤ G:= fun i hi=>(hM i hi).1
 apply tB.n4 G _ (zD.AN G _)
 intro u v w huv huw
 obtain ⟨i,hi,hiv⟩:=(E1 G S H hHG u v).mp huv
 obtain ⟨j,hj,hjw⟩:=(E1 G S H hHG u w).mp huw
 by_cases hij: i= j
 · subst j
   exact qJ.gP G (H i) (hM i hi) u v w hiv hjw
 · exact (hdis i hi j hj hij u v w hiv hjw).elim
end Be
end
noncomputable section
namespace Be.C3
variable {N: ℕ} {G M: SimpleGraph (Fin N)} (P: C3 G M)
lemma Lr (u v: Fin N): P.added.Adj u v↔
   ∃i,i≤ P.length∧((u= P.vertex (2*i)∧ v= P.vertex (2*i+1))∨
     (u= P.vertex (2*i+1)∧ v= P.vertex (2*i))):= by
 constructor
 · rintro ⟨_,h⟩
   obtain ⟨i,hi,he⟩:= mem_image.mp h
   exact ⟨i,by have h:=mem_range.mp hi;omega,Sym2.eq_iff.mp he.symm⟩
 · rintro ⟨i,hi,h⟩
   have he: s(u,v)= s(P.vertex (2*i),P.vertex (2*i+1)):= Sym2.eq_iff.mpr h
   refine ⟨(G.adj_congr_of_sym2 he).mpr (P.Mu (2*i) (by omega)),?_⟩
   exact mem_image.mpr ⟨i,mem_range.mpr (by omega),he.symm⟩
lemma Di: Matching G P.added:= by
 apply tB.n4 G _ (zD.AN G _)
 intro u v w huv huw
 obtain ⟨i,hi,huv⟩:=(P.Lr u v).mp huv
 obtain ⟨j,hj,huw⟩:=(P.Lr u w).mp huw
 rcases huv with ⟨hu,hv⟩|⟨hu,hv⟩<;> rcases huw with ⟨hu',hw⟩|⟨hu',hw⟩
 · have hij:= P.injective (2*i) (2*j) (by omega) (by omega) (hu.symm.trans hu')
   have he: i= j:= by omega
   rw [he] at hv
   exact hv.trans hw.symm
 · have hij:= P.injective (2*i) (2*j+1) (by omega) (by omega) (hu.symm.trans hu')
   omega
 · have hij:= P.injective (2*i+1) (2*j) (by omega) (by omega) (hu.symm.trans hu')
   omega
 · have hij:= P.injective (2*i+1) (2*j+1) (by omega) (by omega) (hu.symm.trans hu')
   have he: i= j:= by omega
   rw [he] at hv
   exact hv.trans hw.symm
lemma KZ: P.Nm≤ M:= by
 intro u v huv
 obtain ⟨i,hi,he⟩:= mem_image.mp huv.2
 have hi': i< P.length:= mem_range.mp hi
 have hm: M.Adj (P.vertex (2*i+1)) (P.vertex (2*i+2)):= by
   have hh:=(P.MG (2*i+1) (by omega)).mpr ⟨i,by omega⟩
   convert hh using 1
 exact (M.adj_congr_of_sym2 he).mp hm
lemma Dh: Disjoint M.edgeFinset P.added.edgeFinset:= by
 apply disjoint_left.mpr
 intro e heM heA
 rw [P.IT] at heA
 obtain ⟨i,hi,rfl⟩:= mem_image.mp heA
 have hm:= M.mem_edgeSet.mp (M.mem_edgeFinset.mp heM)
 have hodd:=(P.MG (2*i) (by have h:=mem_range.mp hi;omega)).mp hm
 obtain ⟨j,hj⟩:= hodd
 omega
lemma Im (i: ℕ) (hi: i< P.length):
   P.Nm.Adj (P.vertex (2*i+1)) (P.vertex (2*i+2)):= by
 refine ⟨?_,mem_image.mpr ⟨i,mem_range.mpr hi,rfl⟩⟩
 convert P.Mu (2*i+1) (by omega) using 1
lemma Cx (hM: Matching G M):
   ∀u v w,P.added.Adj u v→ M.Adj u w→ P.Nm.Adj u w:= by
 intro u v w huv huw
 obtain ⟨i,hi,h⟩:=(P.Lr u v).mp huv
 rcases h with ⟨rfl,_⟩|⟨rfl,_⟩
 · by_cases hi0: i= 0
   · subst i
     exact (P.Ki w huw).elim
   · have hip: i-1< P.length:= by omega
     have hrem:= P.Im (i-1) hip
     have hmat:= P.KZ hrem
     have h2: 2*(i-1)+2= 2*i:= by omega
     rw [h2] at hrem hmat
     have hw:= qJ.gP G M hM (P.vertex (2*i)) w (P.vertex (2*(i-1)+1)) huw hmat.symm
     exact hw.symm ▸hrem.symm
 · by_cases hil: i= P.length
   · subst i
     exact (P.LP w huw).elim
   · have hip: i< P.length:= by omega
     have hrem:= P.Im i hip
     have hmat:= P.KZ hrem
     have hw:= qJ.gP G M hM (P.vertex (2*i+1)) w (P.vertex (2*i+2)) huw hmat
     exact hw.symm ▸hrem
lemma Bo (hM: Matching G M):
   Matching G (exchange M P.Nm P.added)∧
   matchingSize (exchange M P.Nm P.added)= matchingSize M+1:= by
 refine ⟨wY G M P.Nm P.added hM P.Di (P.Cx hM),?_⟩
 apply FL M P.Nm P.added P.KZ P.Dh 1
 rw [P.J7,P.Io]
end Be.C3
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
namespace C3
variable (P: C3 G M)
lemma Hr (i: ℕ) (hi: i≤ 2*P.length) (v: Fin N)
   (hv: v∈ s(P.vertex i,P.vertex (i+1))): v∈ P.support:= by
 rcases Sym2.mem_iff.mp hv with h| h
 · exact mem_image.mpr ⟨i,mem_range.mpr (by omega),h.symm⟩
 · exact mem_image.mpr ⟨i+1,mem_range.mpr (by omega),h.symm⟩
lemma Fp (e: Sym2 (Fin N)) (he: e∈ P.added.edgeFinset) (v: Fin N) (hv: v∈ e): v∈ P.support:= by
 rw [P.IT] at he
 obtain ⟨i,hi,rfl⟩:= mem_image.mp he
 exact P.Hr (2*i) (by have h:=mem_range.mp hi;omega) v hv
lemma Cz (e: Sym2 (Fin N)) (he: e∈ P.Nm.edgeFinset) (v: Fin N) (hv: v∈ e): v∈ P.support:= by
 rw [P.Gx] at he
 obtain ⟨i,hi,rfl⟩:= mem_image.mp he
 apply P.Hr (2*i+1) (by have h:=mem_range.mp hi;omega) v
 convert hv using 1
end C3
lemma mQ (H K: SimpleGraph (Fin N)) (S T: Finset (Fin N)) (hd: Disjoint S T)
   (hH:∀e∈ H.edgeFinset,∀v∈ e,v∈ S) (hK:∀e∈ K.edgeFinset,∀v∈ e,v∈ T):
   Disjoint H.edgeFinset K.edgeFinset:= by
 apply disjoint_left.mpr
 intro e heH heK
 obtain ⟨⟨u,v⟩,he⟩:= e.exists_rep
 have hu: u∈ e:= by rw [←he]; exact Sym2.mem_mk_left _ _
 exact disjoint_left.mp hd (hH e heH u hu) (hK e heK u hu)
section Parallel
variable {I: Type} (F: Finset I) (P: I→ C3 G M)
   (hd: Set.Pairwise (F:Set I) (fun i j=> Disjoint (P i).support (P j).support))
include hd in
lemma l0: Set.Pairwise (F:Set I) (fun i j=> Disjoint (P i).added.edgeFinset (P j).added.edgeFinset):= by
 intro i hi j hj hij
 exact mQ _ _ _ _ (hd hi hj hij) (P i).Fp (P j).Fp
include hd in
lemma jG: Set.Pairwise (F:Set I) (fun i j=> Disjoint (P i).Nm.edgeFinset (P j).Nm.edgeFinset):= by
 intro i hi j hj hij
 exact mQ _ _ _ _ (hd hi hj hij) (P i).Cz (P j).Cz
include hd in
lemma nJ (hM: Matching G M):
   let R:= Ld G F (fun i=>(P i).Nm)
   let S:= Ld G F (fun i=>(P i).added)
   Matching G (exchange M R S)∧ matchingSize (exchange M R S)= matchingSize M+F.card:= by
 dsimp only
 let R:= Ld G F (fun i=>(P i).Nm)
 let S:= Ld G F (fun i=>(P i).added)
 have hRG:∀i∈ F,(P i).Nm≤ G:= fun _ _=> zD.AN G _
 have hSG:∀i∈ F,(P i).added≤ G:= fun _ _=> zD.AN G _
 have hR: R≤ M:= by
   intro u v h
   obtain ⟨i,hi,hiv⟩:=(E1 G F _ hRG u v).mp h
   exact (P i).KZ hiv
 have hS: Matching G S:= by
   apply s3 G F _ (fun i _=>(P i).Di)
   intro i hi j hj hij u v w hiv hjw
   have hu:=(P i).Fp s(u,v) ((P i).added.mem_edgeFinset.mpr ((P i).added.mem_edgeSet.mpr hiv)) u (Sym2.mem_mk_left _ _)
   have hu':=(P j).Fp s(u,w) ((P j).added.mem_edgeFinset.mpr ((P j).added.mem_edgeSet.mpr hjw)) u (Sym2.mem_mk_left _ _)
   exact disjoint_left.mp (hd hi hj hij) hu hu'
 have hremove:∀u v w,S.Adj u v→ M.Adj u w→ R.Adj u w:= by
   intro u v w huv huw
   obtain ⟨i,hi,hiv⟩:=(E1 G F _ hSG u v).mp huv
   exact (E1 G F _ hRG u w).mpr ⟨i,hi,(P i).Cx hM u v w hiv huw⟩
 have hdis: Disjoint M.edgeFinset S.edgeFinset:= by
   apply disjoint_left.mpr
   intro e heM heS
   rw [A5 G F _ hSG] at heS
   obtain ⟨i,hi,he⟩:= mem_biUnion.mp heS
   exact disjoint_left.mp (P i).Dh heM he
 refine ⟨wY G M R S hM hS hremove,?_⟩
 apply FL M R S hR hdis F.card
 have hRs:= CW G F (fun i=>(P i).Nm) hRG (jG F P hd)
 have hSs:= CW G F (fun i=>(P i).added) hSG (l0 F P hd)
 change matchingSize S= matchingSize R+F.card
 rw [hRs,hSs]
 simp only [C3.J7,C3.Io,sum_add_distrib,sum_const,nsmul_eq_mul,mul_one]
 norm_cast
end Parallel
end Be
end
noncomputable section
namespace Be
variable {N: ℕ}
lemma BF (G M: SimpleGraph (Fin N)) (hM: Matching G M) (D: Finset (Fin N)):
   Matching (Dy G D) (Dy M D):= by
 apply tB.n4
 · intro u v h
   exact ⟨hM.1 h.1,h.2⟩
 · intro u v w hv hw
   exact qJ.gP G M hM u v w hv.1 hw.1
namespace C3
variable {G M: SimpleGraph (Fin N)}
lemma MB (P Q: C3 G M) (hl: P.length= Q.length) (hv: P.vertex= Q.vertex): P= Q:= by
 cases P
 cases Q
 cases hl
 cases hv
 rfl
variable (D: Finset (Fin N)) (P: C3 (Dy G D) (Dy M D))
lemma iU (v: Fin N) (hv: v∈ P.support): v∉ D:= by
 obtain ⟨i,hi,rfl⟩:= mem_image.mp hv
 have hi': i≤ 2*P.length+1:= by have h:=mem_range.mp hi;omega
 by_cases hi0: i= 0
 · subst i
   exact (P.Mu 0 (by omega)).2.1
 · have hh:=(P.Mu (i-1) (by omega)).2.2
   rwa [show i-1+1= i by omega] at hh
variable (hclosed:∀u,u∈ D→∀v,M.Adj u v→ v∈ D)
include hclosed in
def EN: C3 G M where
 length:= P.length
 vertex:= P.vertex
 injective:= P.injective
 Mu:= fun i hi=>(P.Mu i hi).1
 MG:= by
   intro i hi
   constructor
   · intro hm
     exact (P.MG i hi).mp ⟨hm,
       P.iU D _ (P.Hr i hi _ (Sym2.mem_mk_left _ _)),
       P.iU D _ (P.Hr i hi _ (Sym2.mem_mk_right _ _))⟩
   · intro hodd
     exact ((P.MG i hi).mpr hodd).1
 Ki:= by
   intro w hm
   have hfirst:= P.iU D (P.vertex 0) (P.Hr 0 (by omega) _ (Sym2.mem_mk_left _ _))
   have hw: w∉ D:= by
     intro hw
     exact hfirst (hclosed w hw (P.vertex 0) hm.symm)
   exact P.Ki w ⟨hm,hfirst,hw⟩
 LP:= by
   intro w hm
   have hlast:= P.iU D (P.vertex (2*P.length+1))
     (P.Hr (2*P.length) le_rfl _ (Sym2.mem_mk_right _ _))
   have hw: w∉ D:= by
     intro hw
     exact hlast (hclosed w hw (P.vertex (2*P.length+1)) hm.symm)
   exact P.LP w ⟨hm,hlast,hw⟩
include hclosed in
lemma g3: Function.Injective (fun Q: C3 (Dy G D) (Dy M D)=> Q.EN D hclosed):= by
 intro Q R he
 exact Q.MB R (congrArg (fun X: C3 G M=> X.length) he) (congrArg (fun X: C3 G M=> X.vertex) he)
end C3
end Be
end
noncomputable section
namespace Be
variable {N: ℕ}
lemma BA (G M K: SimpleGraph (Fin N)) (hM: Matching G M) (hK: Matching G K):
   ∃F: Finset (C3 G M),
     Set.Pairwise (F: Set (C3 G M)) (fun P Q=> Disjoint P.support Q.support)∧
     matchingSize K≤ matchingSize M+F.card:= by
 have aux:∀t: ℕ,∀(G M K: SimpleGraph (Fin N)),Matching G M→ Matching G K→
     matchingSize M+matchingSize K= t→
     ∃F: Finset (C3 G M),
       Set.Pairwise (F: Set (C3 G M)) (fun P Q=> Disjoint P.support Q.support)∧
       matchingSize K≤ matchingSize M+F.card:= by
   intro t
   induction t using Nat.strong_induction_on with
   | h t ih =>
     intro G M K hM hK ht
     by_cases hsmall: matchingSize K≤ matchingSize M
     · refine ⟨∅,?_,by simpa using hsmall⟩
       intro P hP
       simp at hP
     · have hsurplus: matchingSize M< matchingSize K:= by omega
       obtain ⟨r,w,hfree,hw⟩:= iN G M K hM hK hsurplus
       obtain ⟨P,hmax⟩:= JT.D9 (comparison M K) r
       have hlen:= P.mH hmax hfree w hw
       let D:= P.support
       let G':= Dy G D
       let M':= Dy M D
       let K':= Dy K D
       have hm':= BF G M hM D
       have hk':= BF G K hK D
       have hmcount:= P.oT hmax hM hK hfree hlen
       have hkcount:= P.oS hmax hM hK hfree hlen
       have hdec: matchingSize M'+matchingSize K'< t:= by dsimp [M',K',D];omega
       obtain ⟨F0,hd0,hbound0⟩:= ih (matchingSize M'+matchingSize K') hdec G' M' K' hm' hk' rfl
       have hclosed:∀u,u∈ D→∀v,M.Adj u v→ v∈ D:= P.q0 hmax hM hK hfree hlen
       let f: C3 G' M'→ C3 G M:= fun Q=> Q.EN D hclosed
       let F: Finset (C3 G M):= F0.image f
       have hinj: Function.Injective f:= C3.g3 D hclosed
       have hcard: F.card= F0.card:= card_image_of_injective F0 hinj
       have hd: Set.Pairwise (F: Set (C3 G M)) (fun Q R=> Disjoint Q.support R.support):= by
         intro Q hQ R hR hne
         obtain ⟨Q0,hQ0,rfl⟩:= mem_image.mp hQ
         obtain ⟨R0,hR0,rfl⟩:= mem_image.mp hR
         exact hd0 hQ0 hR0 (fun h=> hne (congrArg f h))
       have hout:∀Q∈ F,∀v∈ Q.support,v∉ D:= by
         intro Q hQ v hv
         obtain ⟨Q0,hQ0,rfl⟩:= mem_image.mp hQ
         exact Q0.iU D v hv
       by_cases hodd: Odd P.length
       · let A:= P.wP hmax hM hK hfree hodd
         have hAsupport: A.support= D:= P.eW hmax hM hK hfree hodd
         have hAdis:∀Q∈ F,Disjoint A.support Q.support:= by
           intro Q hQ
           rw [hAsupport]
           exact disjoint_left.mpr (fun v hvD hvQ=> hout Q hQ v hvQ hvD)
         have hAnot: A∉ F:= by
           intro hA
           have h0: A.vertex 0∈ A.support:= mem_image.mpr ⟨0,mem_range.mpr (by omega),rfl⟩
           have hD: A.vertex 0∈ D:= hAsupport ▸h0
           exact hout A hA _ h0 hD
         refine ⟨insert A F,?_,?_⟩
         · intro Q hQ R hR hne
           rcases mem_insert.mp hQ with hQ|hQ
           · subst Q
             rcases mem_insert.mp hR with hR|hR
             · exact (hne hR.symm).elim
             · exact hAdis R hR
           · rcases mem_insert.mp hR with hR|hR
             · subst R
               exact (hAdis Q hQ).symm
             · exact hd hQ hR hne
         · rw [card_insert_of_notMem hAnot,hcard]
           rw [Nat.odd_iff] at hodd
           dsimp [M',K',D] at hbound0
           omega
       · refine ⟨F,hd,?_⟩
         rw [hcard]
         rw [Nat.odd_iff] at hodd
         dsimp [M',K',D] at hbound0
         omega
 exact aux _ G M K hM hK rfl
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
lemma dN (F: Finset (C3 G M))
   (hd: Set.Pairwise (F: Set (C3 G M)) (fun P Q=> Disjoint P.support Q.support)):
   (∑P∈ F,P.length)≤ matchingSize M:= by
 have hsub: F.biUnion (fun P=> P.Nm.edgeFinset) ⊆M.edgeFinset:= by
   intro e he
   obtain ⟨P,hP,he⟩:= mem_biUnion.mp he
   exact SimpleGraph.edgeFinset_mono P.KZ he
 have hh:= card_le_card hsub
 have hrem: Set.Pairwise (F: Set (C3 G M)) (fun P Q=> Disjoint P.Nm.edgeFinset Q.Nm.edgeFinset):=
   jG F id hd
 rw [card_biUnion hrem] at hh
 have heq:(∑P∈ F,P.Nm.edgeFinset.card)=∑P∈ F,P.length:=
   sum_congr rfl (fun P _=> P.Io)
 rwa [heq] at hh
lemma c8 (hM: Matching G M) (k: ℕ)
   (hNo:∀P: C3 G M,k< P.length):
   (k+1)*optimum G≤(k+2)*matchingSize M:= by
 obtain ⟨K,hK,hKsize⟩:= qJ.F9 G
 obtain ⟨F,hd,hpack⟩:= BA G M K hM hK
 have hlength:= dN F hd
 have hlong:(k+1)*F.card≤∑P∈ F,P.length:= by
   calc
     _=∑_∈ F,(k+1):= by simp [mul_comm]
     _≤∑P∈ F,P.length:= sum_le_sum (fun P _=> Nat.succ_le_of_lt (hNo P))
 rw [hKsize] at hpack
 nlinarith
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
namespace Bi
variable {root: Fin N} (S: Bi G M root)
lemma Ak (e: Sym2 (Fin N)) (he: e∈ S.HP) (v: Fin N) (hv: v∈ e): v∈ S.vertices:= by
 change e∈(S.NS.filter (fun p=> M.Adj p.1 p.2)).image (fun p=> s(p.1,p.2)) at he
 obtain ⟨p,hp,hpe⟩:= mem_image.mp he
 rw [←hpe] at hv
 have hends:= S.Ft p.1 p.2 (mem_filter.mp hp).1
 rcases Sym2.mem_iff.mp hv with hv|hv
 · exact hv.symm ▸hends.1
 · exact hv.symm ▸hends.2
end Bi
section Family
variable {I: Type} (F: Finset I) (roots: I→ Fin N) (S:∀i,Bi G M (roots i))
   (hd: Set.Pairwise (F:Set I) (fun i j=> Disjoint (S i).vertices (S j).vertices))
include hd in
lemma h5: Set.Pairwise (F:Set I) (fun i j=> Disjoint (S i).HP (S j).HP):= by
 intro i hi j hj hij
 apply disjoint_left.mpr
 intro e hei hej
 obtain ⟨⟨u,v⟩,he⟩:= e.exists_rep
 have hu: u∈ e:= by rw [←he];exact Sym2.mem_mk_left _ _
 exact disjoint_left.mp (hd hi hj hij) ((S i).Ak e hei u hu) ((S j).Ak e hej u hu)
include hd in
lemma h6:(∑i∈ F,(S i).HP.card)≤ matchingSize M:= by
 have hsub: F.biUnion (fun i=>(S i).HP) ⊆M.edgeFinset:= by
   intro e he
   obtain ⟨i,hi,he⟩:= mem_biUnion.mp he
   exact (S i).rV he
 have hcard:= card_le_card hsub
 rw [card_biUnion (h5 F roots S hd)] at hcard
 exact hcard
include hd in
lemma i7 (limit: ℕ) (hlarge:∀i∈ F,limit+1≤(S i).vertices.card):
   F.card*limit≤ 2*matchingSize M:= by
 have hbound (i: I) (hi: i∈ F): limit≤ 2*(S i).HP.card:= by
   have hv:=(S i).E5
   have hl:= hlarge i hi
   omega
 calc
   _=∑_∈ F,limit:= by simp [mul_comm]
   _≤∑i∈ F,2*(S i).HP.card:= sum_le_sum hbound
   _= 2*∑i∈ F,(S i).HP.card:= by rw [mul_sum]
   _≤ 2*matchingSize M:= Nat.mul_le_mul_left 2 (h6 F roots S hd)
end Family
end Be
end
noncomputable section
namespace Be
lemma wT {I V: Type} [DecidableEq V] (F: Finset I) (S: I→ Finset V) (D: Finset V)
   (hdis: Set.Pairwise (F:Set I) (fun i j=> Disjoint (S i) (S j)))
   (hhit:∀i∈ F,(S i ∩D).Nonempty): F.card≤ D.card:= by
 have hd: Set.Pairwise (F:Set I) (fun i j=> Disjoint (S i ∩D) (S j ∩D)):= by
   intro i hi j hj hij
   exact (hdis hi hj hij).mono inter_subset_left inter_subset_left
 have hsub: F.biUnion (fun i=> S i ∩D) ⊆D:= by
   intro v hv
   obtain ⟨i,_,hv⟩:= mem_biUnion.mp hv
   exact (mem_inter.mp hv).2
 calc
   F.card=∑_∈ F,(1:ℕ):= by simp
   _≤∑i∈ F,(S i ∩D).card:= sum_le_sum (fun i hi=> Nat.one_le_iff_ne_zero.mpr (card_ne_zero.mpr (hhit i hi)))
   _=(F.biUnion (fun i=> S i ∩D)).card:=(card_biUnion hd).symm
   _≤ D.card:= card_le_card hsub
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
namespace C3
variable (P: C3 G M)
lemma IB: P.support.card= 2*P.length+2:= by
 unfold support
 rw [card_image_of_injOn]
 · exact card_range _
 · intro i hi j hj he
   exact P.injective i j (by have h:=mem_range.mp hi;omega) (by have h:=mem_range.mp hj;omega) he
lemma sL (hM: Matching G M) (u: Fin N) (hu: u∈ P.support) (w: Fin N) (huw: M.Adj u w):
   P.Nm.Adj u w:= by
 obtain ⟨i,hi,rfl⟩:= mem_image.mp hu
 have hi': i≤ 2*P.length+1:= by have h:=mem_range.mp hi;omega
 have hi0: 0< i:= by
   by_contra h
   have he: i= 0:= by omega
   subst i
   exact P.Ki w huw
 have hiend: i< 2*P.length+1:= by
   by_contra h
   have he: i= 2*P.length+1:= by omega
   rw [he] at huw
   exact P.LP w huw
 let j:=(i-1)/2
 have hj: j< P.length:= by dsimp [j];omega
 have hij: i= 2*j+1∨ i= 2*j+2:= by dsimp [j];omega
 have hm:=(P.MG (2*j+1) (by omega)).mpr (show Odd (2*j+1) from ⟨j,by omega⟩)
 have heM: P.Nm.Adj (P.vertex (2*j+1)) (P.vertex (2*j+2)):= by
   apply P.Nm.mem_edgeSet.mp
   apply P.Nm.mem_edgeFinset.mp
   rw [P.Gx]
   exact mem_image.mpr ⟨j,mem_range.mpr hj,rfl⟩
 rcases hij with hij|hij
 · rw [hij] at huw ⊢
   have he:= qJ.gP G M hM _ _ _ huw hm
   rw [he]
   exact heM
 · rw [hij] at huw ⊢
   have he:= qJ.gP G M hM _ _ _ huw hm.symm
   rw [he]
   exact heM.symm
lemma B7 (hM: Matching G M) (u: Fin N) (hu: u∈ P.support) (w: Fin N) (huw: M.Adj u w):
   w∈ P.support:= by
 have hr:= P.sL hM u hu w huw
 exact P.Cz s(u,w) (P.Nm.mem_edgeFinset.mpr (P.Nm.mem_edgeSet.mpr hr)) w (Sym2.mem_mk_right _ _)
end C3
def Gp (F: Finset (C3 G M)): Finset (Fin N):= F.biUnion C3.support
lemma pK (hM: Matching G M) (F: Finset (C3 G M)):
   ∀u,u∈ Gp F→∀w,M.Adj u w→ w∈ Gp F:= by
 intro u hu w huw
 obtain ⟨P,hP,hu⟩:= mem_biUnion.mp hu
 exact mem_biUnion.mpr ⟨P,hP,P.B7 hM u hu w huw⟩
lemma u6 (F: Finset (C3 G M))
   (hd: Set.Pairwise (F: Set (C3 G M)) (fun P Q=> Disjoint P.support Q.support)):
   (Gp F).card= 2*(∑P∈ F,P.length)+2*F.card:= by
 unfold Gp
 rw [card_biUnion hd]
 simp only [C3.IB,sum_add_distrib,←mul_sum,sum_const,smul_eq_mul]
 ring
lemma nG (hM: Matching G M) (F: Finset (C3 G M)):
   FW M (Gp F)= F.biUnion (fun P=> P.Nm.edgeFinset):= by
 ext e
 constructor
 · intro he
   obtain ⟨he,u,hu,hue⟩:= mem_filter.mp he
   obtain ⟨P,hP,hu⟩:= mem_biUnion.mp hu
   obtain ⟨w,hew⟩:= Sym2.mem_iff_exists.mp hue
   have hm: M.Adj u w:= M.mem_edgeSet.mp (by rw [←hew];exact M.mem_edgeFinset.mp he)
   have hr:= P.sL hM u hu w hm
   refine mem_biUnion.mpr ⟨P,hP,?_⟩
   rw [hew]
   exact P.Nm.mem_edgeFinset.mpr (P.Nm.mem_edgeSet.mpr hr)
 · intro he
   obtain ⟨P,hP,he⟩:= mem_biUnion.mp he
   obtain ⟨⟨u,v⟩,hev⟩:= e.exists_rep
   have hu: u∈ e:= by rw [←hev];exact Sym2.mem_mk_left _ _
   exact mem_filter.mpr ⟨SimpleGraph.edgeFinset_mono P.KZ he,u,
     mem_biUnion.mpr ⟨P,hP,P.Cz e he u hu⟩,hu⟩
lemma sC (hM: Matching G M) (F: Finset (C3 G M))
   (hd: Set.Pairwise (F: Set (C3 G M)) (fun P Q=> Disjoint P.support Q.support)):
   matchingSize (Dy M (Gp F))+(∑P∈ F,P.length)= matchingSize M:= by
 have hh:= Hq M (Gp F)
 have hrem: Set.Pairwise (F: Set (C3 G M)) (fun P Q=> Disjoint P.Nm.edgeFinset Q.Nm.edgeFinset):=
   jG F id hd
 rw [nG hM F,card_biUnion hrem] at hh
 have heq:(∑P∈ F,P.Nm.edgeFinset.card)=∑P∈ F,P.length:= sum_congr rfl (fun P _=> P.Io)
 rwa [heq] at hh
lemma nA (hM: Matching G M) (F: Finset (C3 G M)) (k: ℕ)
   (hmax:∀P: C3 G M,P.length≤ k→∃Q∈ F,¬Disjoint P.support Q.support):
   ∀P: C3 (Dy G (Gp F)) (Dy M (Gp F)),k< P.length:= by
 intro P
 by_contra hlen
 let R:= P.EN (Gp F) (pK hM F)
 obtain ⟨Q,hQ,hdis⟩:= hmax R (by change P.length≤ k;omega)
 apply hdis
 apply disjoint_left.mpr
 intro v hvR hvQ
 exact P.iU (Gp F) v hvR (mem_biUnion.mpr ⟨Q,hQ,hvQ⟩)
lemma k4 (G: SimpleGraph (Fin N)) (D: Finset (Fin N)):
   optimum G≤ optimum (Dy G D)+D.card:= by
 obtain ⟨K,hK,hKs⟩:= qJ.F9 G
 have hk':= BF G K hK D
 have hsize:= qJ.gQ (Dy G D) (Dy K D) hk'
 have hdel:= Hq K D
 have hdis: Set.Pairwise (FW K D: Set (Sym2 (Fin N))) (fun e f=> Disjoint e.toFinset f.toFinset):= by
   intro e he f hf hne
   apply disjoint_left.mpr
   intro v hve hvf
   exact hK.2 ⟨e,K.mem_edgeFinset.mp (mem_filter.mp he).1⟩ (mem_univ _)
     ⟨f,K.mem_edgeFinset.mp (mem_filter.mp hf).1⟩ (mem_univ _)
     (fun h=> hne (congrArg Subtype.val h)) v (Sym2.mem_toFinset.mp hve) (Sym2.mem_toFinset.mp hvf)
 have hhit:∀e∈ FW K D,(e.toFinset ∩D).Nonempty:= by
   intro e he
   obtain ⟨v,hv,hve⟩:=(mem_filter.mp he).2
   exact ⟨v,mem_inter.mpr ⟨Sym2.mem_toFinset.mpr hve,hv⟩⟩
 have hcard:= wT (FW K D) Sym2.toFinset D hdis hhit
 omega
end Be
end
noncomputable section
namespace Be
variable {N: ℕ}
structure tI (G M: SimpleGraph (Fin N)) (ell: ℕ) where
 MG: Matching G M
 ND: G8 G M
 labels: Fin N ×Fin N→ ℕ
 Nm: Finset (Fin N)
 NV: SimpleGraph (Fin N)
 found: Finset (C3 G M)
 MF: NV≤ G
 HK:∀u v,NV.Adj u v→ u∉ Nm∧ v∉ Nm
 HQ:∀u v,M.Adj u v→ u∉ Nm→ NV.Adj u v
 EL:∀u,u∈ Nm→∀v,M.Adj u v→ v∈ Nm
 DQ: Set.Pairwise (found: Set (C3 G M)) (fun P Q=> Disjoint P.support Q.support)
 Hu: Gp found ⊆Nm
 DO:∀r S,ND.state r= some S→ Disjoint S.tree.vertices Nm
 I9:∀r S,ND.state r= some S→∀u v,(u,v)∈ S.tree.NS→ NV.Adj u v
 Iu:∀r,(∀w,¬M.Adj r w)→ r∉ Nm→∃S,ND.state r= some S
 labelled: ND.Mq ell labels
 complete: ND.qK
 positive:∀a,1≤ labels a
 upper:∀a,labels a≤ ell+1
namespace tI
variable {G M: SimpleGraph (Fin N)} {ell: ℕ} (S: tI G M ell)
lemma vI (r: Fin N) (R: Lp G M r) (hR: S.ND.state r= some R): r∉ S.Nm:= by
 intro hr
 exact disjoint_left.mp (S.DO r R hR) R.tree.MU hr
lemma k7 (r: Fin N) (R: Lp G M r) (hR: S.ND.state r= some R)
   (v: Fin N) (hv: v∈ R.tree.vertices): v∉ S.Nm:= by
 intro hr
 exact disjoint_left.mp (S.DO r R hR) hv hr
def initial (G M: SimpleGraph (Fin N)) (hM: Matching G M) (ell: ℕ): tI G M ell where
 MG:= hM
 ND:= G8.initial G M
 labels _:= ell+1
 Nm:=∅
 NV:= G
 found:=∅
 MF:= le_rfl
 HK:= by intro u v h;simp
 HQ:= fun _ _ hm _=> hM.1 hm
 EL:= by intro u hu;simp at hu
 DQ:= by intro P hP;simp at hP
 Hu:= by simp [Gp]
 DO:= by intro r R hR;simp
 I9:= by
   intro r R hR u v he
   change (if h:∀w,¬M.Adj r w then some (Lp.initial G M r h) else none)= some R at hR
   split_ifs at hR with hf
   cases Option.some.inj hR
   change (u,v)∈(∅: Finset (Fin N ×Fin N)) at he
   simp at he
 Iu:= by
   intro r hf hr
   exact ⟨Lp.initial G M r hf,by simp [G8.initial,hf]⟩
 labelled:= G8.Ab G M ell _
 complete:= by
   intro r R hR
   change (if h:∀w,¬M.Adj r w then some (Lp.initial G M r h) else none)= some R at hR
   split_ifs at hR with hf
   cases Option.some.inj hR
   intro P i hi
   have hh:=(P.Mu i hi).2
   change (P.vertex i,P.vertex (i+1))∈(∅: Finset (Fin N ×Fin N))∨
     (P.vertex (i+1),P.vertex i)∈(∅: Finset (Fin N ×Fin N)) at hh
   simp at hh
 positive:= by intro a;omega
 upper:= fun _=> le_rfl
end tI
end Be
end
noncomputable section
namespace Be
structure tF where
 history: y6
 consistent: history.JS
 KB: history.JX
 root: Fin history.keys.card
 state: Lp history.graph history.MG root
 complete: state.tree.qK
namespace tF
def leader (A: tF): ℕ:=A.history.identity A.root
def members (A: tF): Finset ℕ:=A.state.tree.vertices.image A.history.identity
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)} (A: tF)
   (S: tI G M ell) (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (out: Fin N→ Option ℕ) (hOut: ReportsMatching G ids out M)
def Represents: Prop:=
 ∃hAuth: A.history.Li G ids out,
   S.ND.state ((A.history.embedding hAuth hi hOut A.KB).toFun A.root)=
     some (A.state.Nd (A.history.embedding hAuth hi hOut A.KB))
end tF
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G H M: SimpleGraph (Fin N)}
lemma qR (E: Finset (Fin N ×Fin N)) (hE:∀u v,(u,v)∈ E→ H.Adj u v):
   Mv G E≤ H:= by
 intro u v h
 rcases h.2 with he|he
 · exact hE u v he
 · exact (hE v u he).symm
namespace Bi
variable {alpha beta: Fin N} (A: Bi G M alpha) (B: Bi G M beta)
lemma bH
   (hA:∀u v,(u,v)∈ A.NS→ H.Adj u v) (hB:∀u v,(u,v)∈ B.NS→ H.Adj u v)
   (hNo:¬Nonempty (C3 H M)) (u v: Fin N) (huv: H.Adj u v):
   ¬Nonempty (C3 (Mv G ((A.NS ∪B.NS) ∪{(u,v)})) M):= by
 apply pI _ hNo
 apply qR
 intro x y he
 rcases mem_union.mp he with he|he
 · rcases mem_union.mp he with he|he
   · exact hA x y he
   · exact hB x y he
 · obtain ⟨hx,hy⟩:= Prod.mk.inj (mem_singleton.mp he)
   rw [hx,hy]
   exact huv
lemma cH (hdis: Disjoint A.vertices B.vertices)
   (hA:∀u v,(u,v)∈ A.NS→ H.Adj u v) (hB:∀u v,(u,v)∈ B.NS→ H.Adj u v)
   (hNo:¬Nonempty (C3 H M)) (a b: Fin N ×Fin N)
   (ha: A.Reaches a) (hb: B.Reaches b) (huv: H.Adj a.2 b.2)
   (hG: G.Adj a.2 b.2) (hM:¬M.Adj a.2 b.2): False:= by
 exact A.bH B hA hB hNo a.2 b.2 huv
   (A.cP B hdis a b ha hb hG hM)
end Bi
end Be
end
noncomputable section
namespace Be.G8
variable {N: ℕ} {G M: SimpleGraph (Fin N)} (F: G8 G M)
variable {alpha beta: Fin N}
def E2 (A: Lp G M alpha) (B: Lp G M beta):
   (r: Fin N)→ Option (Lp G M r):=
 Function.update (Function.update F.state alpha (some A)) beta (some B)
lemma CZ (hab: alpha≠ beta) (A: Lp G M alpha) (B: Lp G M beta):
   F.E2 A B alpha= some A:= by simp [E2,hab]
lemma E3 (A: Lp G M alpha) (B: Lp G M beta):
   F.E2 A B beta= some B:= by simp [E2]
lemma C0 (A: Lp G M alpha) (B: Lp G M beta) (r: Fin N)
   (hra: r≠ alpha) (hrb: r≠ beta): F.E2 A B r= F.state r:= by
 simp [E2,hra,hrb]
def K1 (hab: alpha≠ beta) (A: Lp G M alpha) (B: Lp G M beta)
   (hA: F.state alpha= some A) (hB: F.state beta= some B)
   (A': Lp G M alpha) (B': Lp G M beta)
   (hd: Disjoint A'.tree.vertices B'.tree.vertices)
   (hp: A'.tree.vertices ∪B'.tree.vertices ⊆A.tree.vertices ∪B.tree.vertices): G8 G M where
 state:= F.E2 A' B'
 disjoint:= by
   intro r s hrs R S hR hS
   have hout (t: Fin N) (hta: t≠ alpha) (htb: t≠ beta)
       (T: Lp G M t) (hT: F.state t= some T):
       Disjoint (A.tree.vertices ∪B.tree.vertices) T.tree.vertices:= by
     apply disjoint_union_left.mpr
     exact ⟨F.disjoint alpha t hta.symm A T hA hT,F.disjoint beta t htb.symm B T hB hT⟩
   have hasub: A'.tree.vertices ⊆A.tree.vertices ∪B.tree.vertices:= subset_union_left.trans hp
   have hbsub: B'.tree.vertices ⊆A.tree.vertices ∪B.tree.vertices:= subset_union_right.trans hp
   by_cases hra: r= alpha
   · subst r
     rw [F.CZ hab] at hR
     cases Option.some.inj hR
     by_cases hsb: s= beta
     · subst s
       rw [F.E3] at hS
       cases Option.some.inj hS
       exact hd
     · have hsa: s≠ alpha:= hrs.symm
       rw [F.C0 A' B' s hsa hsb] at hS
       exact (hout s hsa hsb S hS).mono hasub (subset_refl _)
   · by_cases hrb: r= beta
     · subst r
       rw [F.E3] at hR
       cases Option.some.inj hR
       by_cases hsa: s= alpha
       · subst s
         rw [F.CZ hab] at hS
         cases Option.some.inj hS
         exact hd.symm
       · have hsb: s≠ beta:= hrs.symm
         rw [F.C0 A' B' s hsa hsb] at hS
         exact (hout s hsa hsb S hS).mono hbsub (subset_refl _)
     · rw [F.C0 A' B' r hra hrb] at hR
       by_cases hsa: s= alpha
       · subst s
         rw [F.CZ hab] at hS
         cases Option.some.inj hS
         exact ((hout r hra hrb R hR).mono hasub (subset_refl _)).symm
       · by_cases hsb: s= beta
         · subst s
           rw [F.E3] at hS
           cases Option.some.inj hS
           exact ((hout r hra hrb R hR).mono hbsub (subset_refl _)).symm
         · rw [F.C0 A' B' s hsa hsb] at hS
           exact F.disjoint r s hrs R S hR hS
lemma sN (hab: alpha≠ beta) (A: Lp G M alpha) (B: Lp G M beta)
   (hA: F.state alpha= some A) (hB: F.state beta= some B)
   (A': Lp G M alpha) (B': Lp G M beta)
   (hd: Disjoint A'.tree.vertices B'.tree.vertices)
   (hp: A'.tree.vertices ∪B'.tree.vertices ⊆A.tree.vertices ∪B.tree.vertices)
   (ell: ℕ) (lab lab': Fin N ×Fin N→ ℕ) (hF: F.Mq ell lab)
   (hmono:∀a,lab' a≤ lab a) (hA': A'.Mq ell lab') (hB': B'.Mq ell lab'):
   (F.K1 hab A B hA hB A' B' hd hp).Mq ell lab':= by
 intro r S hS
 change F.E2 A' B' r= some S at hS
 by_cases hra: r= alpha
 · subst r
   rw [F.CZ hab] at hS
   cases Option.some.inj hS
   exact hA'
 · by_cases hrb: r= beta
   · subst r
     rw [F.E3] at hS
     cases Option.some.inj hS
     exact hB'
   · rw [F.C0 A' B' r hra hrb] at hS
     exact S.F5 ell lab lab' (hF r S hS) hmono
def Jy (D: Finset (Fin N)): G8 G M where
 state r:= if r∈ D then none else F.state r
 disjoint:= by
   intro r s hrs A B hA hB
   split_ifs at hA with hr
   split_ifs at hB with hs
   exact F.disjoint r s hrs A B hA hB
lemma pQ (D: Finset (Fin N)) (ell: ℕ) (labels: Fin N ×Fin N→ ℕ)
   (hF: F.Mq ell labels):(F.Jy D).Mq ell labels:= by
 intro r S hS
 change (if r∈ D then none else F.state r)= some S at hS
 split_ifs at hS with hr
 exact hF r S hS
end Be.G8
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
lemma Bi.iA {root: Fin N} (T: Bi G M root) (hM: Matching G M)
   (u: Fin N) (hu: u∈ T.vertices) (v: Fin N) (huv: M.Adj u v): v∈ T.vertices:= by
 rcases T.wS u hu with hu|hu
 · rw [hu] at huv
   exact (T.L9 v huv).elim
 · obtain ⟨w,hm,hw⟩:= T.Hm u hu
   have he:= qJ.gP G M hM u v w huv hm
   exact he.symm ▸hw
namespace tI
variable {ell: ℕ} (S: tI G M ell) {alpha beta: Fin N}
def augment (hab: alpha≠ beta) (A: Lp G M alpha) (B: Lp G M beta)
   (hA: S.ND.state alpha= some A) (hB: S.ND.state beta= some B)
   (P: C3 G M) (hP: P.support ⊆A.tree.vertices ∪B.tree.vertices): tI G M ell:= by
 let D:= A.tree.vertices ∪B.tree.vertices
 let F:= S.ND.Jy {alpha,beta}
 have hDclosed:∀u,u∈ D→∀v,M.Adj u v→ v∈ D:= by
   intro u hu v huv
   rcases mem_union.mp hu with hu|hu
   · exact mem_union_left _ (A.tree.iA S.MG u hu v huv)
   · exact mem_union_right _ (B.tree.iA S.MG u hu v huv)
 have hDoutside: Disjoint D S.Nm:= disjoint_union_left.mpr ⟨S.DO alpha A hA,S.DO beta B hB⟩
 have hother:∀r R,F.state r= some R→ S.ND.state r= some R∧ r≠ alpha∧ r≠ beta:= by
   intro r R hR
   change (if r∈({alpha,beta}:Finset (Fin N)) then none else S.ND.state r)= some R at hR
   split_ifs at hR with hr
   simp only [mem_insert,mem_singleton,not_or] at hr
   exact ⟨hR,hr⟩
 have hsep:∀r R,F.state r= some R→ Disjoint R.tree.vertices D:= by
   intro r R hR
   obtain ⟨hR,hra,hrb⟩:= hother r R hR
   exact disjoint_union_right.mpr ⟨S.ND.disjoint r alpha hra R A hR hA,S.ND.disjoint r beta hrb R B hR hB⟩
 have hpout: Disjoint P.support S.Nm:= hDoutside.mono hP (subset_refl _)
 exact {
   MG:= S.MG
   ND:= F
   labels:= S.labels
   Nm:= S.Nm ∪D
   NV:= Dy S.NV D
   found:= insert P S.found
   MF:= fun _ _ h=> S.MF h.1
   HK:= by
     intro u v h
     have ho:= S.HK u v h.1
     exact ⟨by simpa only [mem_union,not_or] using And.intro ho.1 h.2.1,
       by simpa only [mem_union,not_or] using And.intro ho.2 h.2.2⟩
   HQ:= by
     intro u v huv hu
     have hou: u∉ S.Nm∧ u∉ D:= by simpa only [mem_union,not_or] using hu
     refine ⟨S.HQ u v huv hou.1,hou.2,?_⟩
     intro hvD
     exact hou.2 (hDclosed v hvD u huv.symm)
   EL:= by
     intro u hu v huv
     rcases mem_union.mp hu with hu|hu
     · exact mem_union_left _ (S.EL u hu v huv)
     · exact mem_union_right _ (hDclosed u hu v huv)
   DQ:= by
     have hdisP:∀Q∈ S.found,Disjoint P.support Q.support:= by
       intro Q hQ
       apply hpout.mono (subset_refl _)
       intro v hv
       exact S.Hu (mem_biUnion.mpr ⟨Q,hQ,hv⟩)
     intro Q hQ R hR hne
     rcases mem_insert.mp hQ with hQ|hQ
     · subst Q
       rcases mem_insert.mp hR with hR|hR
       · exact (hne hR.symm).elim
       · exact hdisP R hR
     · rcases mem_insert.mp hR with hR|hR
       · subst R
         exact (hdisP Q hQ).symm
       · exact S.DQ hQ hR hne
   Hu:= by
     intro v hv
     obtain ⟨Q,hQ,hv⟩:= mem_biUnion.mp hv
     rcases mem_insert.mp hQ with hQ|hQ
     · subst Q
       exact mem_union_right _ (hP hv)
     · exact mem_union_left _ (S.Hu (mem_biUnion.mpr ⟨Q,hQ,hv⟩))
   DO:= by
     intro r R hR
     exact disjoint_union_right.mpr ⟨S.DO r R (hother r R hR).1,hsep r R hR⟩
   I9:= by
     intro r R hR u v he
     have hE:= S.I9 r R (hother r R hR).1 u v he
     have huv:= R.tree.Ft u v he
     refine ⟨hE,?_,?_⟩
     · intro hu
       exact disjoint_left.mp (hsep r R hR) huv.1 hu
     · intro hv
       exact disjoint_left.mp (hsep r R hR) huv.2 hv
   Iu:= by
     intro r hf hr
     have hout: r∉ S.Nm∧ r∉ D:= by simpa only [mem_union,not_or] using hr
     obtain ⟨R,hR⟩:= S.Iu r hf hout.1
     have hra: r≠ alpha:= by intro he;subst r;exact hout.2 (mem_union_left _ A.tree.MU)
     have hrb: r≠ beta:= by intro he;subst r;exact hout.2 (mem_union_right _ B.tree.MU)
     refine ⟨R,?_⟩
     change (if r∈({alpha,beta}:Finset (Fin N)) then none else S.ND.state r)= some R
     simp only [mem_insert,mem_singleton,hra,hrb,or_self,if_false]
     exact hR
   labelled:= S.ND.pQ _ ell S.labels S.labelled
   complete:= by
     intro r R hR
     exact S.complete r R (hother r R hR).1
   positive:= S.positive
   upper:= S.upper}
end tI
end Be
end
noncomputable section
namespace Be.tI
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ} (S: tI G M ell)
   {alpha beta: Fin N}
def JB (hab: alpha≠ beta) (A: Lp G M alpha) (B: Lp G M beta)
   (hA: S.ND.state alpha= some A) (hB: S.ND.state beta= some B)
   (A': Lp G M alpha) (B': Lp G M beta)
   (hd: Disjoint A'.tree.vertices B'.tree.vertices)
   (hp: A'.tree.vertices ∪B'.tree.vertices ⊆A.tree.vertices ∪B.tree.vertices)
   (hLiveA:∀u v,(u,v)∈ A'.tree.NS→ S.NV.Adj u v)
   (hLiveB:∀u v,(u,v)∈ B'.tree.NS→ S.NV.Adj u v)
   (hCompleteA: A'.tree.qK) (hCompleteB: B'.tree.qK)
   (lab: Fin N ×Fin N→ ℕ) (hmono:∀a,lab a≤ S.labels a) (hpos:∀a,1≤ lab a)
   (hLabelA: A'.Mq ell lab) (hLabelB: B'.Mq ell lab): tI G M ell:= by
 let F:= S.ND.K1 hab A B hA hB A' B' hd hp
 have haSub: A'.tree.vertices ⊆A.tree.vertices ∪B.tree.vertices:= subset_union_left.trans hp
 have hbSub: B'.tree.vertices ⊆A.tree.vertices ∪B.tree.vertices:= subset_union_right.trans hp
 have holdOut: Disjoint (A.tree.vertices ∪B.tree.vertices) S.Nm:=
   disjoint_union_left.mpr ⟨S.DO alpha A hA,S.DO beta B hB⟩
 exact {
   MG:= S.MG
   ND:= F
   labels:= lab
   Nm:= S.Nm
   NV:= S.NV
   found:= S.found
   MF:= S.MF
   HK:= S.HK
   HQ:= S.HQ
   EL:= S.EL
   DQ:= S.DQ
   Hu:= S.Hu
   DO:= by
     intro r R hR
     change S.ND.E2 A' B' r= some R at hR
     by_cases hra: r= alpha
     · subst r
       rw [S.ND.CZ hab] at hR
       cases Option.some.inj hR
       exact holdOut.mono haSub (subset_refl _)
     · by_cases hrb: r= beta
       · subst r
         rw [S.ND.E3] at hR
         cases Option.some.inj hR
         exact holdOut.mono hbSub (subset_refl _)
       · rw [S.ND.C0 A' B' r hra hrb] at hR
         exact S.DO r R hR
   I9:= by
     intro r R hR
     change S.ND.E2 A' B' r= some R at hR
     by_cases hra: r= alpha
     · subst r
       rw [S.ND.CZ hab] at hR
       cases Option.some.inj hR
       exact hLiveA
     · by_cases hrb: r= beta
       · subst r
         rw [S.ND.E3] at hR
         cases Option.some.inj hR
         exact hLiveB
       · rw [S.ND.C0 A' B' r hra hrb] at hR
         exact S.I9 r R hR
   Iu:= by
     intro r hf hr
     by_cases hra: r= alpha
     · subst r
       exact ⟨A',S.ND.CZ hab A' B'⟩
     · by_cases hrb: r= beta
       · subst r
         exact ⟨B',S.ND.E3 A' B'⟩
       · obtain ⟨R,hR⟩:= S.Iu r hf hr
         exact ⟨R,(S.ND.C0 A' B' r hra hrb).trans hR⟩
   labelled:= S.ND.sN hab A B hA hB A' B' hd hp ell S.labels lab S.labelled hmono hLabelA hLabelB
   complete:= by
     intro r R hR
     change S.ND.E2 A' B' r= some R at hR
     by_cases hra: r= alpha
     · subst r
       rw [S.ND.CZ hab] at hR
       cases Option.some.inj hR
       exact hCompleteA
     · by_cases hrb: r= beta
       · subst r
         rw [S.ND.E3] at hR
         cases Option.some.inj hR
         exact hCompleteB
       · rw [S.ND.C0 A' B' r hra hrb] at hR
         exact S.complete r R hR
   positive:= hpos
   upper:= fun a=>(hmono a).trans (S.upper a)}
end Be.tI
end
noncomputable section
namespace Be.Bi
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {root: Fin N} (T: Bi G M root)
lemma r7 (H: SimpleGraph (Fin N)) (hH:∀u v,(u,v)∈ T.NS→ H.Adj u v):
   ∀u v,(u,v)∈ T.normalized.NS→ H.Adj u v:= by
 intro u v he
 rcases T.Gk (u,v) he with he|he
 · exact hH u v he
 · exact (hH v u he).symm
lemma dS (C: Finset (Fin N ×Fin N)) (hC:∀u v,(u,v)∈ C→ G.Adj u v)
   (hTC: T.NS ⊆C) (H: SimpleGraph (Fin N)) (hH:∀u v,(u,v)∈ C→ H.Adj u v):
   ∀u v,(u,v)∈(T.FX C hC).normalized.NS→ H.Adj u v:= by
 apply (T.FX C hC).r7 H
 intro u v he
 exact hH u v (T.o0 C hC hTC he)
end Be.Bi
end
noncomputable section
namespace Be.G6
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {alpha beta: Fin N} (D: G6 G M alpha beta)
lemma eL:¬D.right.Reaches D.target.swap:= by
 intro hreach
 obtain ⟨Q,hQl,hQlast⟩:= hreach
 let P':= D.NX.Kt D.KC (fun i hi=> D.BX (D.inside i hi))
 let Q':= Q.NM (Fs _ _ D.AO)
 have hd: Disjoint P'.support Q'.support:= D.disjoint.mono
   (D.left.EA D.NX D.inside) (D.right.nD Q)
 have hhead: Q.vertex (2*Q.length)= D.target.1:= by
   have hh: Q.vertex (2*(Q.length-1)+2)= D.target.1:= congrArg Prod.snd hQlast
   rwa [show 2*(Q.length-1)+2= 2*Q.length by omega] at hh
 have hbridge:(Mv G D.KC).Adj (P'.vertex (2*P'.length)) (Q'.vertex (2*Q'.length)):= by
   change G.Adj (D.NX.vertex (2*D.NX.length)) (Q.vertex (2*Q.length))∧
     ((D.NX.vertex (2*D.NX.length),Q.vertex (2*Q.length))∈ D.KC∨
      (Q.vertex (2*Q.length),D.NX.vertex (2*D.NX.length))∈ D.KC)
   rw [hhead]
   exact ⟨D.Nz,Or.inl (mem_union_right _ (by simp))⟩
 have hunmatched:¬M.Adj (P'.vertex (2*P'.length)) (Q'.vertex (2*Q'.length)):= by
   change ¬M.Adj (D.NX.vertex (2*D.NX.length)) (Q.vertex (2*Q.length))
   rw [hhead]
   exact D.zV
 exact D.Ck ⟨P'.Ac Q' hd hbridge hunmatched⟩
lemma a2:
   ¬Fk (Mv G D.right.NS) M beta D.target.swap:= D.eL
end Be.G6
end
noncomputable section
namespace Be.G6
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {alpha beta: Fin N} (D: G6 G M alpha beta)
lemma gR (hS: D.right.qK) (e: Fin N ×Fin N)
   (he: D.right.Reaches e) (hrev: D.right.Reaches e.swap) (hmoved: e∈ D.H1):
   e.swap∈ D.H1:= by
 have hDom: G2 (Mv G D.right.NS) M beta D.target e:= by
   intro P hPl hLast hAvoid
   have hr:=(D.right.b9 hS {D.target} e).mpr ⟨P,hPl,hAvoid,hLast⟩
   exact (mem_sdiff.mp hmoved).2 hr
 have hDomRev:= wV D.MG D.target e D.a2 he hDom
 have hmem:= D.right.mJ hS e.swap hrev
 have hmatch:= D.right.Cv e.swap hrev
 refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨hmem,hmatch⟩,?_⟩
 intro hr
 obtain ⟨P,hPl,hAvoid,hLast⟩:=(D.right.b9 hS {D.target} e.swap).mp hr
 exact hDomRev P hPl hLast hAvoid
lemma xW (hS: D.right.qK) (e: Fin N ×Fin N)
   (he: D.right.Reaches e) (hrev: D.right.Reaches e.swap):
   e∈ D.H1↔ e.swap∈ D.H1:= by
 constructor
 · exact D.gR hS e he hrev
 · intro hr
   have hh:= D.gR hS e.swap hrev (by simpa only [Prod.swap_swap] using he) hr
   simpa only [Prod.swap_swap] using hh
lemma lQ (hS: D.right.qK) (e: Fin N ×Fin N)
   (he: D.right.Reaches e) (hrev: D.right.Reaches e.swap):
   (D.JM.Reaches e∧ D.JM.Reaches e.swap)∨
   (D.remaining.Reaches e∧ D.remaining.Reaches e.swap):= by
 have hmatch:= D.right.Cv e he
 have hmatchRev:= D.right.Cv e.swap hrev
 by_cases hmoved: e∈ D.H1
 · have hmovedRev:=(D.xW hS e he hrev).mp hmoved
   exact Or.inl ⟨D.JM.EE e (D.Au (D.Gd e hmoved)) hmatch,
     D.JM.EE e.swap (D.Au (D.Gd e.swap hmovedRev)) hmatchRev⟩
 · have hnotRev: e.swap∉ D.H1:= fun h=> hmoved ((D.xW hS e he hrev).mpr h)
   have hRet (a: Fin N ×Fin N) (ha: D.right.Reaches a) (hnot: a∉ D.H1): a∈ D.remaining.NS:= by
     have hmem:= D.right.mJ hS a ha
     have hm:= D.right.Cv a ha
     by_cases hr: a∈ D.right.CD {D.target}
     · exact mem_union_left _ hr
     · exact (hnot (mem_sdiff.mpr ⟨mem_filter.mpr ⟨hmem,hm⟩,hr⟩)).elim
   exact Or.inr ⟨D.remaining.EE e (hRet e he hmoved) hmatch,
     D.remaining.EE e.swap (hRet e.swap hrev hnotRev) hmatchRev⟩
end Be.G6
end
noncomputable section
namespace Be.v9
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {root: Fin N} (P: v9 G M root)
lemma zJ (u v: Fin N) (hbridge: G.Adj (P.vertex (2*P.length)) u) (hmatch: G.Adj u v)
   (i: ℕ) (hi: i< 2*(P.length+1)): G.Adj (P.He u v i) (P.He u v (i+1)):= by
 by_cases hi0: i< 2*P.length
 · rw [P.zK u v i (by omega),P.zK u v (i+1) (by omega)]
   exact P.Mu i hi0
 · rcases (show i= 2*P.length∨ i= 2*P.length+1 by omega) with rfl|rfl
   · rw [P.zK u v (2*P.length) le_rfl,P.wJ]
     exact hbridge
   · rw [P.wJ,show 2*P.length+1+1= 2*P.length+2 by omega,P.wI]
     exact hmatch
lemma l6 (u v: Fin N) (hbridge:¬M.Adj (P.vertex (2*P.length)) u) (hmatch: M.Adj u v)
   (i: ℕ) (hi: i< 2*(P.length+1)): M.Adj (P.He u v i) (P.He u v (i+1))↔ Odd i:= by
 by_cases hi0: i< 2*P.length
 · rw [P.zK u v i (by omega),P.zK u v (i+1) (by omega)]
   exact P.MG i hi0
 · rcases (show i= 2*P.length∨ i= 2*P.length+1 by omega) with rfl|rfl
   · rw [P.zK u v (2*P.length) le_rfl,P.wJ]
     constructor
     · exact fun h=>(hbridge h).elim
     · rintro ⟨j,hj⟩
       omega
   · rw [P.wJ,show 2*P.length+1+1= 2*P.length+2 by omega,P.wI]
     exact ⟨fun _=>⟨P.length,by omega⟩,fun _=> hmatch⟩
def Fq (u v: Fin N) (hGbridge: G.Adj (P.vertex (2*P.length)) u) (hGmatch: G.Adj u v)
   (hMbridge:¬M.Adj (P.vertex (2*P.length)) u) (hMmatch: M.Adj u v)
   (hu: u∉ P.support) (hv: v∉ P.support): v9 G M root where
 length:= P.length+1
 vertex:= P.He u v
 first:=(P.zK u v 0 (by omega)).trans P.first
 injective:= P.jW u v hu hv hMmatch.ne
 Mu:= P.zJ u v hGbridge hGmatch
 MG:= P.l6 u v hMbridge hMmatch
 L9:= P.L9
lemma l3 (u v: Fin N) (hGbridge: G.Adj (P.vertex (2*P.length)) u) (hGmatch: G.Adj u v)
   (hMbridge:¬M.Adj (P.vertex (2*P.length)) u) (hMmatch: M.Adj u v)
   (hu: u∉ P.support) (hv: v∉ P.support):
   P.M4 (P.Fq u v hGbridge hGmatch hMbridge hMmatch hu hv):= by
 exact ⟨by change P.length≤ P.length+1;omega,fun i hi=> P.zK u v i hi⟩
lemma tM (u v: Fin N) (hGbridge: G.Adj (P.vertex (2*P.length)) u) (hGmatch: G.Adj u v)
   (hMbridge:¬M.Adj (P.vertex (2*P.length)) u) (hMmatch: M.Adj u v)
   (hu: u∉ P.support) (hv: v∉ P.support):
   (P.Fq u v hGbridge hGmatch hMbridge hMmatch hu hv).KA P.length=(u,v):= by
 change (P.He u v (2*P.length+1),P.He u v (2*P.length+2))= _
 rw [P.wJ,P.wI]
lemma oC (u v: Fin N) (hGbridge: G.Adj (P.vertex (2*P.length)) u) (hGmatch: G.Adj u v)
   (hMbridge:¬M.Adj (P.vertex (2*P.length)) u) (hMmatch: M.Adj u v)
   (hu: u∉ P.support) (hv: v∉ P.support) (E: Finset (Fin N ×Fin N)) (hP: P.Nv E)
   (hbridge:(P.vertex (2*P.length),u)∈ E) (hmatch:(u,v)∈ E):
   (P.Fq u v hGbridge hGmatch hMbridge hMmatch hu hv).Nv E:= by
 intro i hi
 change (P.He u v i,P.He u v (i+1))∈ E
 change i< 2*(P.length+1) at hi
 by_cases hi0: i< 2*P.length
 · rw [P.zK u v i (by omega),P.zK u v (i+1) (by omega)]
   exact hP i hi0
 · rcases (show i= 2*P.length∨ i= 2*P.length+1 by omega) with rfl|rfl
   · rw [P.zK u v (2*P.length) le_rfl,P.wJ]
     exact hbridge
   · rw [P.wJ,show 2*P.length+1+1= 2*P.length+2 by omega,P.wI]
     exact hmatch
end Be.v9
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {alpha beta: Fin N}
namespace G6
variable (D: G6 G M alpha beta)
lemma yX: D.target.1∉ D.NX.support:= by
 intro h
 exact disjoint_left.mp D.disjoint (D.left.EA D.NX D.inside h)
   (D.right.Ft _ _ D.target_mem).1
lemma yW: D.target.2∉ D.NX.support:= by
 intro h
 exact disjoint_left.mp D.disjoint (D.left.EA D.NX D.inside h)
   (D.right.Ft _ _ D.target_mem).2
def K6: v9 G M alpha:= D.NX.Fq D.target.1 D.target.2
 D.Nz (D.MG.1 D.EV) D.zV D.EV D.yX D.yW
lemma yR: D.K6.Nv D.JM.NS:=
 D.NX.oC D.target.1 D.target.2 D.Nz (D.MG.1 D.EV)
   D.zV D.EV D.yX D.yW D.Ne
   (fun i hi=> D.BY (D.inside i hi)) D.Dp D.EW
lemma yT: D.K6.KA D.NX.length= D.target:=
 D.NX.tM D.target.1 D.target.2 D.Nz (D.MG.1 D.EV)
   D.zV D.EV D.yX D.yW
lemma yS (ell: ℕ) (lab: Fin N ×Fin N→ ℕ)
   (hbound: D.NX.length+1≤ ell) (hEligible: D.NX.length+1< lab D.target):
   D.K6.Mq ell (D.K6.Nl lab)∧ D.K6.Nl lab D.target< lab D.target:= by
 refine ⟨D.K6.AL lab ell hbound,?_⟩
 rw [←D.yT]
 exact D.K6.EI lab D.NX.length (by change D.NX.length< D.NX.length+1;omega)
   (by rw [D.yT];exact hEligible)
end G6
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
namespace v9
variable {root: Fin N} (P: v9 G M root)
def J4: Finset (Fin N ×Fin N):=(range P.length).image P.KA
lemma jF (k n: ℕ) (hn: n≤ P.length): P.L5 k n ⊆P.J4:= by
 intro a ha
 obtain ⟨i,hi,rfl⟩:= mem_image.mp ha
 exact mem_image.mpr ⟨i,mem_range.mpr (by have hh:=(mem_Ico.mp hi).2;omega),rfl⟩
end v9
namespace C2
variable {alpha beta: Fin N} (D: C2 G M alpha beta)
end C2
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
namespace v9
variable {root: Fin N} (P: v9 G M root)
lemma EH (lab: Fin N ×Fin N→ ℕ) (a: Fin N ×Fin N)
   (ha:∀i,i< P.length→ P.KA i≠ a): P.Nl lab a= lab a:= by
 unfold Nl
 exact dif_neg (by rintro ⟨i,hi,he⟩;exact ha i hi he)
lemma yH (lab: Fin N ×Fin N→ ℕ) (i: ℕ) (hi: i< P.length)
   (hshort: P.Nl lab (P.KA i)< i+1):
   P.Nl lab (P.KA i)= lab (P.KA i)∧ lab (P.KA i)< i+1:= by
 rw [P.KX lab i hi] at hshort ⊢
 by_cases hh: lab (P.KA i)≤ i+1
 · rw [min_eq_left hh] at hshort ⊢
   exact ⟨rfl,hshort⟩
 · rw [min_eq_right (by omega)] at hshort
   omega
lemma I4 {Q: v9 G M root} (hext: P.M4 Q) (i: ℕ) (hi: i< P.length):
   Q.KA i= P.KA i:=
 Prod.ext (hext.2 (2*i+1) (by omega)) (hext.2 (2*i+2) (by omega))
end v9
def IN {root: Fin N} (S: Bi G M root) (P: v9 G M root)
   (lab: Fin N ×Fin N→ ℕ): Prop:=
 ∀i,i< P.length→ lab (P.KA i)< i+1→ S.Reaches (P.KA i).swap
namespace Bi
variable {alpha beta: Fin N} (A: Bi G M alpha) (B: Bi G M beta)
end Bi
namespace Lp
variable {root: Fin N} (S: Lp G M root)
def M5 (lab: Fin N ×Fin N→ ℕ): Prop:=∀P,S.active= some P→ IN S.tree P lab
lemma wK (lab: Fin N ×Fin N→ ℕ) (hS: S.M5 lab): S.backtrack.M5 lab:= by
 intro Q hQ
 change S.active.bind (fun P=> if h: 0< P.length then some (P.take (P.length-1) (by omega)) else none)= some Q at hQ
 cases hP: S.active with
 | none => simp [hP] at hQ
 | some P =>
   simp only [hP,Option.bind_some] at hQ
   split_ifs at hQ with h
   cases Option.some.inj hQ
   intro i hi hshort
   exact hS P hP i (by change i< P.length-1 at hi;omega) hshort
end Lp
end Be
end
noncomputable section
namespace Be.tI
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ} (S: tI G M ell)
   {alpha beta: Fin N}
def Ew (D: C2 G M alpha beta)
   (A: Lp G M alpha) (B: Lp G M beta)
   (hA: S.ND.state alpha= some A) (hB: S.ND.state beta= some B)
   (hAT: A.tree= D.data.left) (hBT: B.tree= D.data.right) (hBactive: B.active= some D.Ng)
   (hBridge: S.NV.Adj (D.data.NX.vertex (2*D.data.NX.length)) D.data.target.1)
   (hEligible: D.data.NX.length+1< S.labels D.data.target): tI G M ell:= by
 let T:= Classical.choice D.transfer
 let C:= D.data.KC
 have hCache:∀u v,(u,v)∈ C→ S.NV.Adj u v:= by
   intro u v he
   rcases mem_union.mp he with he|he
   · rcases mem_union.mp he with he|he
     · exact S.I9 alpha A hA u v (by rw [hAT];exact he)
     · exact S.I9 beta B hB u v (by rw [hBT];exact he)
   · simp only [mem_insert,mem_singleton] at he
     rcases he with he|he
     · obtain ⟨hu,hv⟩:= Prod.mk.inj he
       rw [hu,hv];exact hBridge
     · obtain ⟨hu,hv⟩:= Prod.mk.inj he
       rw [hu,hv];exact hBridge.symm
 have hCG:∀u v,(u,v)∈ C→ G.Adj u v:= fun u v he=> S.MF (hCache u v he)
 let L:=(T.left.FX C hCG).normalized
 let R:=(T.right.FX C hCG).normalized
 have hLv: L.vertices= T.left.vertices:=(T.left.FX C hCG).r8.trans (T.left.kK C hCG)
 have hRv: R.vertices= T.right.vertices:=(T.right.FX C hCG).r8.trans (T.right.kK C hCG)
 have hFull: D.path.Nv L.NS:= by
   intro i hi
   exact (T.left.FX C hCG).Cl (mem_union_left _ (T.active i hi))
 have hQ:(D.Ng.take (D.index-1) (by have hb:=D.bound;omega)).Nv T.right.NS:= by
   rw [T.MT,D.sI]
   exact D.data.right.lB D.Ng D.inside D.index D.positive (by have hb:=D.bound;omega)
 have hRight:(D.Ng.take (D.index-1) (by have hb:=D.bound;omega)).Nv R.NS:= by
   intro i hi
   exact (T.right.FX C hCG).Cl (mem_union_left _ (hQ i hi))
 let A': Lp G M alpha:=
   { tree:= L
     active:= some D.path
     inside:= by intro P hP;cases Option.some.inj hP;exact hFull
     NU:= A.NU
     modified:= true
     extended:= true}
 let B': Lp G M beta:=
   { tree:= R
     active:= some (D.Ng.take (D.index-1) (by have hb:=D.bound;omega))
     inside:= by intro P hP;cases Option.some.inj hP;exact hRight
     NU:= B.NU
     modified:= true
     extended:= B.extended}
 have hd: Disjoint A'.tree.vertices B'.tree.vertices:= by
   change Disjoint L.vertices R.vertices
   rw [hLv,hRv]
   exact T.disjoint
 have hp: A'.tree.vertices ∪B'.tree.vertices ⊆A.tree.vertices ∪B.tree.vertices:= by
   change L.vertices ∪R.vertices ⊆A.tree.vertices ∪B.tree.vertices
   rw [hLv,hRv,hAT,hBT,T.vertices]
 have hLabelOld:= S.labelled beta B hB D.Ng hBactive
 have hLabels:= D.labels ell S.labels hLabelOld hEligible
 have hLabelA: A'.Mq ell (D.path.Nl S.labels):= by
   intro P hP
   cases Option.some.inj hP
   exact hLabels.1
 have hLabelB: B'.Mq ell (D.path.Nl S.labels):= by
   intro P hP
   cases Option.some.inj hP
   exact D.CE ell S.labels hLabelOld
 exact S.JB D.data.distinct A B hA hB A' B' hd hp
   (T.left.dS C hCG T.Jl S.NV hCache)
   (T.right.dS C hCG T.Is S.NV hCache)
   (T.left.FX C hCG).r6 (T.right.FX C hCG).r6
   (D.path.Nl S.labels) (D.path.Ik S.labels) (D.path.AM S.labels S.positive) hLabelA hLabelB
end Be.tI
end
noncomputable section
namespace Be.tI
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ} (S: tI G M ell)
   {alpha beta: Fin N}
def AE (D: G6 G M alpha beta)
   (A: Lp G M alpha) (B: Lp G M beta)
   (hA: S.ND.state alpha= some A) (hB: S.ND.state beta= some B)
   (hAT: A.tree= D.left) (hBT: B.tree= D.right)
   (hInactive:∀Q,B.active= some Q→∀i,i< Q.length→ Q.KA i≠ D.target)
   (hBridge: S.NV.Adj (D.NX.vertex (2*D.NX.length)) D.target.1)
   (hBound: D.NX.length+1≤ ell) (hEligible: D.NX.length+1< S.labels D.target): tI G M ell:= by
 let C:= D.KC
 have hCache:∀u v,(u,v)∈ C→ S.NV.Adj u v:= by
   intro u v he
   rcases mem_union.mp he with he|he
   · rcases mem_union.mp he with he|he
     · exact S.I9 alpha A hA u v (by rw [hAT];exact he)
     · exact S.I9 beta B hB u v (by rw [hBT];exact he)
   · simp only [mem_insert,mem_singleton] at he
     rcases he with he|he
     · obtain ⟨hu,hv⟩:= Prod.mk.inj he
       rw [hu,hv];exact hBridge
     · obtain ⟨hu,hv⟩:= Prod.mk.inj he
       rw [hu,hv];exact hBridge.symm
 have hCG:∀u v,(u,v)∈ C→ G.Adj u v:= fun u v he=> S.MF (hCache u v he)
 let L:=(D.JM.FX C hCG).normalized
 let R:=(D.remaining.FX C hCG).normalized
 have hLv: L.vertices= D.JM.vertices:=
   (D.JM.FX C hCG).r8.trans (D.JM.kK C hCG)
 have hRv: R.vertices= D.remaining.vertices:=
   (D.remaining.FX C hCG).r8.trans (D.remaining.kK C hCG)
 have hLeft: D.K6.Nv L.NS:= by
   intro i hi
   exact (D.JM.FX C hCG).Cl (mem_union_left _ (D.yR i hi))
 have hRight:∀Q,B.active= some Q→ Q.Nv R.NS:= by
   intro Q hQ
   have hOrig: Q.Nv D.right.NS:= by rw [←hBT];exact B.inside Q hQ
   have hRet:= D.right.lC Q hOrig D.target (hInactive Q hQ)
   intro i hi
   exact (D.remaining.FX C hCG).Cl (mem_union_left _ (hRet i hi))
 let A': Lp G M alpha:=
   { tree:= L
     active:= some D.K6
     inside:= by intro P hP;cases Option.some.inj hP;exact hLeft
     NU:= A.NU
     modified:= true
     extended:= true}
 let B': Lp G M beta:=
   { tree:= R
     active:= B.active
     inside:= hRight
     NU:= B.NU
     modified:= B.modified
     extended:= B.extended}
 have hd: Disjoint A'.tree.vertices B'.tree.vertices:= by
   change Disjoint L.vertices R.vertices
   rw [hLv,hRv]
   exact D.p9
 have hp: A'.tree.vertices ∪B'.tree.vertices ⊆A.tree.vertices ∪B.tree.vertices:= by
   change L.vertices ∪R.vertices ⊆A.tree.vertices ∪B.tree.vertices
   rw [hLv,hRv,hAT,hBT,D.v8]
 have hLabels:= D.yS ell S.labels hBound hEligible
 have hLabelA: A'.Mq ell (D.K6.Nl S.labels):= by
   intro P hP
   cases Option.some.inj hP
   exact hLabels.1
 have hLabelB: B'.Mq ell (D.K6.Nl S.labels):=
   B.F5 ell S.labels _ (S.labelled beta B hB) (D.K6.Ik S.labels)
 exact S.JB D.distinct A B hA hB A' B' hd hp
   (D.JM.dS C hCG D.En S.NV hCache)
   (D.remaining.dS C hCG ((D.right.pU _).trans D.AO) S.NV hCache)
   (D.JM.FX C hCG).r6 (D.remaining.FX C hCG).r6
   (D.K6.Nl S.labels) (D.K6.Ik S.labels) (D.K6.AM S.labels S.positive) hLabelA hLabelB
end Be.tI
end
noncomputable section
namespace Be.G8
variable {N: ℕ} {G M: SimpleGraph (Fin N)} (F: G8 G M) {alpha: Fin N}
def K0 (A: Lp G M alpha)
   (hd:∀r,r≠ alpha→∀R,F.state r= some R→ Disjoint A.tree.vertices R.tree.vertices): G8 G M where
 state:= Function.update F.state alpha (some A)
 disjoint:= by
   intro r s hrs R S hR hS
   by_cases hra: r= alpha
   · subst r
     simp only [Function.update_self,Option.some.injEq] at hR
     cases hR
     rw [Function.update_of_ne hrs.symm] at hS
     exact hd s hrs.symm S hS
   · rw [Function.update_of_ne hra] at hR
     by_cases hsa: s= alpha
     · subst s
       simp only [Function.update_self,Option.some.injEq] at hS
       cases hS
       exact (hd r hra R hR).symm
     · rw [Function.update_of_ne hsa] at hS
       exact F.disjoint r s hrs R S hR hS
lemma sM (A: Lp G M alpha)
   (hd:∀r,r≠ alpha→∀R,F.state r= some R→ Disjoint A.tree.vertices R.tree.vertices)
   (ell: ℕ) (lab lab': Fin N ×Fin N→ ℕ) (hF: F.Mq ell lab)
   (hmono:∀a,lab' a≤ lab a) (hA: A.Mq ell lab'):(F.K0 A hd).Mq ell lab':= by
 intro r R hR
 change Function.update F.state alpha (some A) r= some R at hR
 by_cases hra: r= alpha
 · subst r
   simp only [Function.update_self,Option.some.injEq] at hR
   cases hR
   exact hA
 · rw [Function.update_of_ne hra] at hR
   exact R.F5 ell lab lab' (hF r R hR) hmono
end Be.G8
end
noncomputable section
namespace Be.tI
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ} (S: tI G M ell) {alpha: Fin N}
def JC (A: Lp G M alpha) (hA: S.ND.state alpha= some A)
   (A': Lp G M alpha)
   (hd:∀r,r≠ alpha→∀R,S.ND.state r= some R→ Disjoint A'.tree.vertices R.tree.vertices)
   (hOutside: Disjoint A'.tree.vertices S.Nm)
   (hLive:∀u v,(u,v)∈ A'.tree.NS→ S.NV.Adj u v)
   (hComplete: A'.tree.qK)
   (lab: Fin N ×Fin N→ ℕ) (hmono:∀a,lab a≤ S.labels a) (hpos:∀a,1≤ lab a)
   (hLabel: A'.Mq ell lab): tI G M ell:= by
 let F:= S.ND.K0 A' hd
 exact {
   MG:= S.MG
   ND:= F
   labels:= lab
   Nm:= S.Nm
   NV:= S.NV
   found:= S.found
   MF:= S.MF
   HK:= S.HK
   HQ:= S.HQ
   EL:= S.EL
   DQ:= S.DQ
   Hu:= S.Hu
   DO:= by
     intro r R hR
     change Function.update S.ND.state alpha (some A') r= some R at hR
     by_cases hra: r= alpha
     · subst r
       simp only [Function.update_self,Option.some.injEq] at hR
       cases hR
       exact hOutside
     · rw [Function.update_of_ne hra] at hR
       exact S.DO r R hR
   I9:= by
     intro r R hR
     change Function.update S.ND.state alpha (some A') r= some R at hR
     by_cases hra: r= alpha
     · subst r
       simp only [Function.update_self,Option.some.injEq] at hR
       cases hR
       exact hLive
     · rw [Function.update_of_ne hra] at hR
       exact S.I9 r R hR
   Iu:= by
     intro r hf hr
     by_cases hra: r= alpha
     · subst r
       exact ⟨A',Function.update_self ..⟩
     · obtain ⟨R,hR⟩:= S.Iu r hf hr
       exact ⟨R,(Function.update_of_ne hra ..).trans hR⟩
   labelled:= S.ND.sM A' hd ell S.labels lab S.labelled hmono hLabel
   complete:= by
     intro r R hR
     change Function.update S.ND.state alpha (some A') r= some R at hR
     by_cases hra: r= alpha
     · subst r
       simp only [Function.update_self,Option.some.injEq] at hR
       cases hR
       exact hComplete
     · rw [Function.update_of_ne hra] at hR
       exact S.complete r R hR
   positive:= hpos
   upper:= fun a=>(hmono a).trans (S.upper a)}
end Be.tI
end
noncomputable section
namespace Be.Bi
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {root: Fin N}
   (S: Bi G M root) (P: v9 G M root) (hP: P.Nv S.NS)
   (u v: Fin N) (hGbridge: G.Adj (P.vertex (2*P.length)) u) (hGmatch: G.Adj u v)
   (hMbridge:¬M.Adj (P.vertex (2*P.length)) u) (hMmatch: M.Adj u v)
   (hu: u∉ P.support) (hv: v∉ P.support)
def FQ: Finset (Fin N ×Fin N):= S.NS ∪{(P.vertex (2*P.length),u),(u,P.vertex (2*P.length)),(u,v)}
include hGbridge hGmatch in
lemma BK:∀x y,(x,y)∈ S.FQ P u v→ G.Adj x y:= by
 intro x y he
 rcases mem_union.mp he with he|he
 · exact S.valid x y he
 · simp only [mem_insert,mem_singleton] at he
   rcases he with he|he|he
   · obtain ⟨hx,hy⟩:= Prod.mk.inj he
     rw [hx,hy];exact hGbridge
   · obtain ⟨hx,hy⟩:= Prod.mk.inj he
     rw [hx,hy];exact hGbridge.symm
   · obtain ⟨hx,hy⟩:= Prod.mk.inj he
     rw [hx,hy];exact hGmatch
include hMbridge in
lemma w1:∀x y,(x,y)∈ S.FQ P u v→ M.Adj x y→
   (x,y)∈ S.NS∨(x,y)=(u,v):= by
 intro x y he hm
 rcases mem_union.mp he with he|he
 · exact Or.inl he
 · simp only [mem_insert,mem_singleton] at he
   rcases he with he|he|he
   · obtain ⟨hx,hy⟩:= Prod.mk.inj he
     rw [hx,hy] at hm
     exact (hMbridge hm).elim
   · obtain ⟨hx,hy⟩:= Prod.mk.inj he
     rw [hx,hy] at hm
     exact (hMbridge hm.symm).elim
   · exact Or.inr he
include hP hGbridge hGmatch hMbridge hMmatch hu hv in
noncomputable def LF: Bi G M root where
 NS:= S.FQ P u v
 L9:= S.L9
 valid:= S.BK P u v hGbridge hGmatch
 xK:= by
   intro x y he hm
   rcases S.w1 P u v hMbridge x y he hm with he|he
   · obtain ⟨Q,hQl,hQ,hQx,hQy⟩:= S.xK x y he hm
     exact ⟨Q,hQl,fun i hi=> mem_union_left _ (hQ i hi),hQx,hQy⟩
   · let Q:= P.Fq u v hGbridge hGmatch hMbridge hMmatch hu hv
     have hQ: Q.Nv (S.FQ P u v):=
       P.oC u v hGbridge hGmatch hMbridge hMmatch hu hv _
         (fun i hi=> mem_union_left _ (hP i hi)) (mem_union_right _ (by simp)) (mem_union_right _ (by simp))
     have ht: Q.vertex (2*Q.length-1)= u:= by
       change P.He u v (2*(P.length+1)-1)= u
       rw [show 2*(P.length+1)-1= 2*P.length+1 by omega,P.wJ]
     have hh: Q.vertex (2*Q.length)= v:= by
       change P.He u v (2*(P.length+1))= v
       rw [show 2*(P.length+1)= 2*P.length+2 by omega,P.wI]
     obtain ⟨hx,hy⟩:= Prod.mk.inj he
     exact ⟨Q,by change 0< P.length+1;omega,hQ,ht.trans hx.symm,hh.trans hy.symm⟩
 LD:= by
   intro x y he
   have hsub: S.NS ⊆S.FQ P u v:= subset_union_left
   have hhead: P.vertex (2*P.length)∈ S.vertices:= S.EA P hP (P.mem_support _ le_rfl)
   have hcovu: C8 M (S.FQ P u v) u:=⟨u,v,mem_union_right _ (by simp),hMmatch,Or.inl rfl⟩
   have hcovv: C8 M (S.FQ P u v) v:=⟨u,v,mem_union_right _ (by simp),hMmatch,Or.inr rfl⟩
   have old (w: Fin N) (hw: w∈ S.vertices): w= root∨ C8 M (S.FQ P u v) w:= by
     rcases S.wS w hw with hw|hw
     · exact Or.inl hw
     · exact Or.inr (Hn hsub hw)
   rcases mem_union.mp he with he|he
   · exact ⟨old x (S.Ft x y he).1,old y (S.Ft x y he).2⟩
   · simp only [mem_insert,mem_singleton] at he
     rcases he with he|he|he
     · obtain ⟨hx,hy⟩:= Prod.mk.inj he
       rw [hx,hy]
       exact ⟨old _ hhead,Or.inr hcovu⟩
     · obtain ⟨hx,hy⟩:= Prod.mk.inj he
       rw [hx,hy]
       exact ⟨Or.inr hcovu,old _ hhead⟩
     · obtain ⟨hx,hy⟩:= Prod.mk.inj he
       rw [hx,hy]
       exact ⟨Or.inr hcovu,Or.inr hcovv⟩
end Be.Bi
end
noncomputable section
namespace Be.Bi
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {root: Fin N}
lemma G0 {S T: Bi G M root} (hST: S.NS ⊆T.NS): S.vertices ⊆T.vertices:= by
 intro v hv
 rcases mem_union.mp hv with hv|hv
 · exact mem_union_left _ hv
 · obtain ⟨e,he,hv⟩:= mem_biUnion.mp hv
   exact mem_union_right _ (mem_biUnion.mpr ⟨e,hST he,hv⟩)
variable (S: Bi G M root) (P: v9 G M root) (hP: P.Nv S.NS)
   (u v: Fin N) (hGb: G.Adj (P.vertex (2*P.length)) u) (hGm: G.Adj u v)
   (hMb:¬M.Adj (P.vertex (2*P.length)) u) (hMm: M.Adj u v)
   (hu: u∉ P.support) (hv: v∉ P.support)
lemma tY:
   (S.LF P hP u v hGb hGm hMb hMm hu hv).vertices= S.vertices ∪{u,v}:= by
 let T:= S.LF P hP u v hGb hGm hMb hMm hu hv
 have hhead:= S.EA P hP (P.mem_support (2*P.length) le_rfl)
 have hends:∀a b,(a,b)∈ S.FQ P u v→
     a∈ S.vertices ∪{u,v}∧ b∈ S.vertices ∪{u,v}:= by
   intro a b he
   rcases mem_union.mp he with he|he
   · have hh:= S.Ft a b he
     exact ⟨mem_union_left _ hh.1,mem_union_left _ hh.2⟩
   · simp only [mem_insert,mem_singleton] at he
     rcases he with he|he|he
     · obtain ⟨ha,hb⟩:= Prod.mk.inj he
       rw [ha,hb]
       exact ⟨mem_union_left _ hhead,mem_union_right _ (by simp)⟩
     · obtain ⟨ha,hb⟩:= Prod.mk.inj he
       rw [ha,hb]
       exact ⟨mem_union_right _ (by simp),mem_union_left _ hhead⟩
     · obtain ⟨ha,hb⟩:= Prod.mk.inj he
       rw [ha,hb]
       exact ⟨mem_union_right _ (by simp),mem_union_right _ (by simp)⟩
 apply Subset.antisymm
 · intro w hw
   rcases mem_union.mp hw with hw|hw
   · exact mem_union_left _ (mem_union_left _ hw)
   · obtain ⟨e,he,hw⟩:= mem_biUnion.mp hw
     have hh:= hends e.1 e.2 he
     rcases mem_insert.mp hw with hw|hw
     · exact hw.symm ▸hh.1
     · exact (mem_singleton.mp hw).symm ▸hh.2
 · have hold: S.vertices ⊆T.vertices:= G0 subset_union_left
   have hnew:= T.Ft u v (mem_union_right _ (by simp))
   intro w hw
   rcases mem_union.mp hw with hw|hw
   · exact hold hw
   · rcases mem_insert.mp hw with hw|hw
     · exact hw.symm ▸hnew.1
     · exact (mem_singleton.mp hw).symm ▸hnew.2
end Be.Bi
end
noncomputable section
namespace Be.tI
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ} (S: tI G M ell) {alpha: Fin N}
def Kg (A: Lp G M alpha) (hA: S.ND.state alpha= some A)
   (P: v9 G M alpha) (hP: P.Nv A.tree.NS)
   (u v: Fin N) (hBridge: S.NV.Adj (P.vertex (2*P.length)) u)
   (hMbridge:¬M.Adj (P.vertex (2*P.length)) u) (hMmatch: M.Adj u v)
   (hu: u∉ P.support) (hv: v∉ P.support)
   (hOther:∀r,r≠ alpha→∀R,S.ND.state r= some R→ u∉ R.tree.vertices∧ v∉ R.tree.vertices)
   (hBound: P.length+1≤ ell) (hEligible: P.length+1< S.labels (u,v)): tI G M ell:= by
 have hGb:= S.MF hBridge
 have hGm:= S.MG.1 hMmatch
 have huAlive:=(S.HK _ _ hBridge).2
 have hvAlive: v∉ S.Nm:= by
   intro hvD
   exact huAlive (S.EL v hvD u hMmatch.symm)
 have hLiveM:= S.HQ u v hMmatch huAlive
 let T:= A.tree.LF P hP u v hGb hGm hMbridge hMmatch hu hv
 let Q:= P.Fq u v hGb hGm hMbridge hMmatch hu hv
 have hQ: Q.Nv T.NS:= P.oC u v hGb hGm hMbridge hMmatch hu hv _
   (fun i hi=> mem_union_left _ (hP i hi)) (mem_union_right _ (by simp)) (mem_union_right _ (by simp))
 have hLiveT:∀a b,(a,b)∈ T.NS→ S.NV.Adj a b:= by
   intro a b he
   rcases mem_union.mp he with he|he
   · exact S.I9 alpha A hA a b he
   · simp only [mem_insert,mem_singleton] at he
     rcases he with he|he|he
     · obtain ⟨ha,hb⟩:= Prod.mk.inj he
       rw [ha,hb];exact hBridge
     · obtain ⟨ha,hb⟩:= Prod.mk.inj he
       rw [ha,hb];exact hBridge.symm
     · obtain ⟨ha,hb⟩:= Prod.mk.inj he
       rw [ha,hb];exact hLiveM
 let A': Lp G M alpha:=
   { tree:= T.normalized
     active:= some Q
     inside:= by intro R hR;cases Option.some.inj hR;intro i hi;exact T.Cl (hQ i hi)
     NU:= A.NU
     modified:= true
     extended:= true}
 have hVertices: A'.tree.vertices= A.tree.vertices ∪{u,v}:=
   T.r8.trans (A.tree.tY P hP u v hGb hGm hMbridge hMmatch hu hv)
 have hd:∀r,r≠ alpha→∀R,S.ND.state r= some R→ Disjoint A'.tree.vertices R.tree.vertices:= by
   intro r hra R hR
   apply disjoint_left.mpr
   intro w hw hwR
   rw [hVertices] at hw
   rcases mem_union.mp hw with hw|hw
   · exact disjoint_left.mp (S.ND.disjoint alpha r hra.symm A R hA hR) hw hwR
   · rcases mem_insert.mp hw with hw|hw
     · subst w
       exact (hOther r hra R hR).1 hwR
     · have he:= mem_singleton.mp hw
       subst w
       exact (hOther r hra R hR).2 hwR
 have hOutside: Disjoint A'.tree.vertices S.Nm:= by
   rw [hVertices]
   apply disjoint_union_left.mpr
   refine ⟨S.DO alpha A hA,?_⟩
   apply disjoint_left.mpr
   intro w hw hwD
   rcases mem_insert.mp hw with hw|hw
   · exact huAlive (hw ▸hwD)
   · exact hvAlive ((mem_singleton.mp hw) ▸hwD)
 have hLabel: A'.Mq ell (Q.Nl S.labels):= by
   intro R hR
   cases Option.some.inj hR
   exact Q.AL S.labels ell hBound
 exact S.JC A hA A' hd hOutside (T.r7 S.NV hLiveT) T.r6
   (Q.Nl S.labels) (Q.Ik S.labels) (Q.AM S.labels S.positive) hLabel
end Be.tI
end
noncomputable section
namespace Be.G8
variable {N: ℕ} {G M: SimpleGraph (Fin N)} (F: G8 G M)
def owner (v: Fin N): Option (Fin N):= if h:∃r,F.Mm r v then some h.choose else none
lemma KP (r v: Fin N): F.owner v= some r↔ F.Mm r v:= by
 unfold owner
 split_ifs with h
 · constructor
   · intro he
     cases Option.some.inj he
     exact h.choose_spec
   · intro hr
     exact congrArg some (F.BE h.choose r v h.choose_spec hr)
 · constructor
   · intro he;cases he
   · intro hr;exact (h ⟨r,hr⟩).elim
lemma KN (v: Fin N): F.owner v= none↔∀r,¬F.Mm r v:= by
 constructor
 · intro h r hr
   have hs:=(F.KP r v).mpr hr
   rw [h] at hs
   cases hs
 · intro h
   cases hs: F.owner v with
   | none => rfl
   | some r => exact (h r ((F.KP r v).mp hs)).elim
lemma KO (r: Fin N) (R: Lp G M r) (hR: F.state r= some R): F.owner r= some r:=
 (F.KP r r).mpr ⟨R,hR,R.tree.MU⟩
lemma kC (hM: Matching G M) (r u v: Fin N) (hu: F.Mm r u) (huv: M.Adj u v): F.Mm r v:= by
 obtain ⟨R,hR,hu⟩:= hu
 exact ⟨R,hR,R.tree.iA hM u hu v huv⟩
lemma sB (hM: Matching G M) (u v: Fin N) (huv: M.Adj u v): F.owner u= F.owner v:= by
 cases hu: F.owner u with
 | none =>
   have hv: F.owner v= none:= by
     apply (F.KN v).mpr
     intro r hr
     exact (F.KN u).mp hu r (F.kC hM r v u hr huv.symm)
   rw [hv]
 | some r =>
   exact (F.KP r v).mpr (F.kC hM r u v ((F.KP r u).mp hu) huv)|>.symm
end Be.G8
namespace Be.tI
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ} (S: tI G M ell)
end Be.tI
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {alpha beta: Fin N}
namespace C3
variable {H: SimpleGraph (Fin N)} (P: C3 H M)
lemma dI (D: Finset (Fin N))
   (hD:∀u v,H.Adj u v→ u∈ D∧ v∈ D): P.support ⊆D:= by
 intro v hv
 obtain ⟨i,hi,rfl⟩:= mem_image.mp hv
 have hi': i≤ 2*P.length+1:= by have hh:=mem_range.mp hi;omega
 by_cases hi0: i= 0
 · subst i
   exact (hD _ _ (P.Mu 0 (by omega))).1
 · have hh:=(hD _ _ (P.Mu (i-1) (by omega))).2
   rwa [show i-1+1= i by omega] at hh
end C3
namespace Bi
variable (A: Bi G M alpha) (B: Bi G M beta)
def Hj (x y: Fin N): Finset (Fin N ×Fin N):=(A.NS ∪B.NS) ∪{(x,y),(y,x)}
lemma iK (x y: Fin N) (hx: x∈ A.vertices) (hy: y∈ B.vertices)
   (u v: Fin N) (he:(u,v)∈ A.Hj B x y):
   u∈ A.vertices ∪B.vertices∧ v∈ A.vertices ∪B.vertices:= by
 rcases mem_union.mp he with he|he
 · rcases mem_union.mp he with he|he
   · have hh:= A.Ft u v he
     exact ⟨mem_union_left _ hh.1,mem_union_left _ hh.2⟩
   · have hh:= B.Ft u v he
     exact ⟨mem_union_right _ hh.1,mem_union_right _ hh.2⟩
 · simp only [mem_insert,mem_singleton] at he
   rcases he with he|he
   · obtain ⟨hu,hv⟩:= Prod.mk.inj he
     rw [hu,hv]
     exact ⟨mem_union_left _ hx,mem_union_right _ hy⟩
   · obtain ⟨hu,hv⟩:= Prod.mk.inj he
     rw [hu,hv]
     exact ⟨mem_union_right _ hy,mem_union_left _ hx⟩
lemma cR (x y: Fin N) (hx: x∈ A.vertices) (hy: y∈ B.vertices)
   (P: C3 (Mv G (A.Hj B x y)) M): P.support ⊆A.vertices ∪B.vertices:= by
 apply P.dI
 intro u v he
 rcases he.2 with he|he
 · exact A.iK B x y hx hy u v he
 · exact (A.iK B x y hx hy v u he).symm
lemma dO (P: v9 G M alpha) (Q: v9 G M beta)
   (hP: P.Nv A.NS) (hQ: Q.Nv B.NS) (hd: Disjoint A.vertices B.vertices)
   (hG: G.Adj (P.vertex (2*P.length)) (Q.vertex (2*Q.length)))
   (hM:¬M.Adj (P.vertex (2*P.length)) (Q.vertex (2*Q.length))):
   Nonempty (C3 (Mv G (A.Hj B (P.vertex (2*P.length)) (Q.vertex (2*Q.length)))) M):= by
 let C:= A.Hj B (P.vertex (2*P.length)) (Q.vertex (2*Q.length))
 let L:= P.Kt C (fun i hi=> mem_union_left _ (mem_union_left _ (hP i hi)))
 let R:= Q.Kt C (fun i hi=> mem_union_left _ (mem_union_right _ (hQ i hi)))
 have hg:(Mv G C).Adj (L.vertex (2*L.length)) (R.vertex (2*R.length)):= by
   change G.Adj (P.vertex (2*P.length)) (Q.vertex (2*Q.length))∧
     ((P.vertex (2*P.length),Q.vertex (2*Q.length))∈ C∨
      (Q.vertex (2*Q.length),P.vertex (2*P.length))∈ C)
   exact ⟨hG,Or.inl (mem_union_right _ (by simp))⟩
 exact ⟨L.Ac R (hd.mono (A.EA P hP) (B.EA Q hQ)) hg hM⟩
end Bi
end Be
end
noncomputable section
namespace Be.Bi
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {alpha beta: Fin N}
lemma b1 (B: Bi G M beta) (hM: Matching G M)
   (u v: Fin N) (hu: u∈ B.vertices) (huv: M.Adj u v):(u,v)∈ B.NS∨(v,u)∈ B.NS:= by
 rcases B.wS u hu with hu|hu
 · rw [hu] at huv
   exact (B.L9 v huv).elim
 · obtain ⟨a,b,he,hm,hu⟩:= hu
   rcases hu with hu|hu
   · subst u
     have heq:= qJ.gP G M hM a v b huv hm
     rw [heq]
     exact Or.inl he
   · subst u
     have heq:= qJ.gP G M hM b v a huv hm.symm
     rw [heq]
     exact Or.inr he
lemma b4 (A: Bi G M alpha) (B: Bi G M beta)
   (hM: Matching G M) (P: v9 G M alpha) (hP: P.Nv A.NS)
   (hd: Disjoint A.vertices B.vertices) (u v: Fin N) (hu: u∈ B.vertices) (huv: M.Adj u v)
   (hG: G.Adj (P.vertex (2*P.length)) u) (hMu:¬M.Adj (P.vertex (2*P.length)) u)
   (hNo:¬Nonempty (C3 (Mv G (A.Hj B (P.vertex (2*P.length)) u)) M)):
   (u,v)∈ B.NS:= by
 rcases B.b1 hM u v hu huv with he|he
 · exact he
 · obtain ⟨Q,hQl,hQ,hQt,hQh⟩:= B.xK v u he huv.symm
   have hg: G.Adj (P.vertex (2*P.length)) (Q.vertex (2*Q.length)):= by rw [hQh];exact hG
   have hm:¬M.Adj (P.vertex (2*P.length)) (Q.vertex (2*Q.length)):= by rw [hQh];exact hMu
   have ha:= A.dO B P Q hP hQ hd hg hm
   rw [hQh] at ha
   exact (hNo ha).elim
end Be.Bi
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
structure qF (S: tI G M ell) (x y: Fin N) where
 ME: Fin N
 L7: Fin N
 left: Lp G M ME
 right: Lp G M L7
 HJ: S.ND.state ME= some left
 GE: S.ND.state L7= some right
 distinct: ME≠ L7
 M1: x∈ left.tree.vertices
 head_mem: y∈ right.tree.vertices
 IY: S.NV.Adj x y
 zV:¬M.Adj x y
 path: C3 (Mv G (left.tree.Hj right.tree x y)) M
structure y7 (S: tI G M ell) (x y: Fin N) where
 root: Fin N
 state: Lp G M root
 present: S.ND.state root= some state
 J5: v9 G M root
 Lq: state.active= some J5
 NX: v9 G M root
 DL: J5.M4 NX
 inside: NX.Nv state.tree.NS
 labelled: NX.Mq ell S.labels
 NC: NX.vertex (2*NX.length)= x
 MK: state.NU= false
 H9: state.extended= false
 bound: NX.length+1≤ ell
 NW: Fin N
 matched: M.Adj y NW
 Kq: y∉ NX.support
 Kp: NW∉ NX.support
 My: NX.length+1< S.labels (y,NW)
 IY: S.NV.Adj x y
 zV:¬M.Adj x y
namespace tI
variable (S: tI G M ell)
def Bd (x y: Fin N) (honorExtended: Bool): Prop:=
 Nonempty {R: qF S x y// honorExtended= true→ R.left.extended= false}
def sE {x y: Fin N} (R: qF S x y): tI G M ell:=
 S.augment R.distinct R.left R.right R.HJ R.GE
   (R.path.NM (show Mv G (R.left.tree.Hj R.right.tree x y)≤ G from fun _ _ h=> h.1))
   (R.left.tree.cR R.right.tree x y R.M1 R.head_mem R.path)
end tI
namespace y7
variable {S: tI G M ell} {x y: Fin N} (R: y7 S x y)
lemma K5: x∈ R.state.tree.vertices:= by
 have hh:= R.state.tree.EA R.NX R.inside (R.NX.mem_support (2*R.NX.length) le_rfl)
 rwa [R.NC] at hh
lemma Do: S.NV.Adj (R.NX.vertex (2*R.NX.length)) y:= by rw [R.NC];exact R.IY
lemma y1:¬M.Adj (R.NX.vertex (2*R.NX.length)) y:= by rw [R.NC];exact R.zV
lemma k3 (hNo:¬S.Bd x y true) {beta: Fin N}
   (B: Lp G M beta) (hB: S.ND.state beta= some B) (hneq: R.root≠ beta)
   (hy: y∈ B.tree.vertices):
   ¬Nonempty (C3 (Mv G (R.state.tree.Hj B.tree x y)) M):= by
 rintro ⟨P⟩
 let A: qF S x y:=
   { ME:= R.root
     L7:= beta
     left:= R.state
     right:= B
     HJ:= R.present
     GE:= hB
     distinct:= hneq
     M1:= R.K5
     head_mem:= hy
     IY:= R.IY
     zV:= R.zV
     path:= P}
 exact hNo ⟨⟨A,fun _=> R.H9⟩⟩
end y7
namespace G8
variable (F: G8 G M)
lemma Ep (hM: Matching G M) (alpha y v: Fin N) (hyv: M.Adj y v)
   (hy: F.owner y= none∨ F.owner y= some alpha):
   ∀r,r≠ alpha→∀R,F.state r= some R→ y∉ R.tree.vertices∧ v∉ R.tree.vertices:= by
 have howner:= F.sB hM y v hyv
 have hnot (r: Fin N) (hra: r≠ alpha): F.owner y≠ some r:= by
   intro hr
   rcases hy with hy|hy
   · rw [hy] at hr;cases hr
   · have he: alpha= r:= Option.some.inj (hy.symm.trans hr)
     exact hra he.symm
 intro r hra R hR
 constructor
 · intro hyR
   exact hnot r hra ((F.KP r y).mpr ⟨R,hR,hyR⟩)
 · intro hvR
   exact hnot r hra (howner.trans ((F.KP r v).mpr ⟨R,hR,hvR⟩))
end G8
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S: tI G M ell} {x y: Fin N}
inductive Bb (R: y7 S x y) where
 | single (hOwner: S.ND.owner y= none∨ S.ND.owner y= some R.root): Bb R
 | inactive {beta: Fin N} (D: G6 G M R.root beta) (B: Lp G M beta)
     (hB: S.ND.state beta= some B) (hAT: R.state.tree= D.left) (hBT: B.tree= D.right)
     (hStem: D.NX= R.NX) (hTarget: D.target=(y,R.NW))
     (hInactive:∀Q,B.active= some Q→∀i,i< Q.length→ Q.KA i≠ D.target): Bb R
 | active {beta: Fin N} (D: C2 G M R.root beta) (B: Lp G M beta)
     (hB: S.ND.state beta= some B) (hAT: R.state.tree= D.data.left) (hBT: B.tree= D.data.right)
     (hStem: D.data.NX= R.NX) (hTarget: D.data.target=(y,R.NW))
     (hActive: B.active= some D.Ng): Bb R
namespace Bb
variable {R: y7 S x y}
def Nj (A: Bb R): tI G M ell:= by
 cases A with
 | single hOwner =>
   exact S.Kg R.state R.present R.NX R.inside y R.NW R.Do R.y1
     R.matched R.Kq R.Kp
     (S.ND.Ep S.MG R.root y R.NW R.matched hOwner) R.bound R.My
 | inactive D B hB hAT hBT hStem hTarget hInactive =>
   exact S.AE D R.state B R.present hB hAT hBT hInactive
     (by rw [hStem,hTarget];exact R.Do) (by rw [hStem];exact R.bound)
     (by rw [hStem,hTarget];exact R.My)
 | active D B hB hAT hBT hStem hTarget hActive =>
   exact S.Ew D R.state B R.present hB hAT hBT hActive
     (by rw [hStem,hTarget];exact R.Do) (by rw [hStem,hTarget];exact R.My)
lemma FN (R: y7 S x y) (hNo:¬S.Bd x y true): Nonempty (Bb R):= by
 cases hOwner: S.ND.owner y with
 | none => exact ⟨Bb.single (Or.inl hOwner)⟩
 | some beta =>
   by_cases hsame: beta= R.root
   · exact ⟨Bb.single (Or.inr (by simpa only [hsame] using hOwner))⟩
   · obtain ⟨B,hB,hy⟩:=(S.ND.KP beta y).mp hOwner
     have hneq: R.root≠ beta:= fun h=> hsame h.symm
     have hdis:= S.ND.disjoint R.root beta hneq R.state B R.present hB
     have hNoMem:= R.k3 hNo B hB hneq hy
     have hNoStem:¬Nonempty (C3 (Mv G
         (R.state.tree.Hj B.tree (R.NX.vertex (2*R.NX.length)) y)) M):= by
       simpa only [R.NC] using hNoMem
     have hTarget:= R.state.tree.b4 B.tree S.MG R.NX R.inside hdis y R.NW hy R.matched
       (S.MF R.Do) R.y1 hNoStem
     let D: G6 G M R.root beta:=
       { MG:= S.MG
         left:= R.state.tree
         right:= B.tree
         NX:= R.NX
         inside:= R.inside
         disjoint:= hdis
         distinct:= hneq
         target:=(y,R.NW)
         target_mem:= hTarget
         EV:= R.matched
         Nz:= S.MF R.Do
         zV:= R.y1
         Ck:= hNoStem}
     by_cases hActive:∃Q,B.active= some Q∧∃i,i< Q.length∧ Q.KA i=(y,R.NW)
     · obtain ⟨Q,hQ,i,hi,he⟩:= hActive
       let T: C2 G M R.root beta:=
         { data:= D
           Ng:= Q
           inside:= B.inside Q hQ
           index:= i+1
           positive:= by omega
           bound:= by omega
           target:= by simpa only [Nat.add_sub_cancel] using he}
       exact ⟨Bb.active T B hB rfl rfl rfl rfl hQ⟩
     · exact ⟨Bb.inactive D B hB rfl rfl rfl rfl (by
         intro Q hQ i hi he
         exact hActive ⟨Q,hQ,i,hi,he⟩)⟩
end Bb
end Be
end
noncomputable section
namespace Be.G8
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
def Mn (F: G8 G M) (p:∀r,Lp G M r→ Prop): Prop:=∃r R,F.state r= some R∧ p r R
lemma t8 (F H: G8 G M) (p:∀r,Lp G M r→ Prop)
   {alpha: Fin N} (A A': Lp G M alpha) (hA: F.state alpha= some A)
   (heq: H.state= Function.update F.state alpha (some A'))
   (hlocal: p alpha A→ p alpha A') (h: F.Mn p): H.Mn p:= by
 obtain ⟨r,R,hR,hp⟩:= h
 by_cases hra: r= alpha
 · subst r
   cases Option.some.inj (hR.symm.trans hA)
   exact ⟨alpha,A',by rw [heq];exact Function.update_self _ _ _,hlocal hp⟩
 · exact ⟨r,R,by rw [heq,Function.update_of_ne hra];exact hR,hp⟩
lemma t9 (F H: G8 G M) (p:∀r,Lp G M r→ Prop)
   {alpha beta: Fin N} (hab: alpha≠ beta)
   (A: Lp G M alpha) (B: Lp G M beta)
   (hA: F.state alpha= some A) (hB: F.state beta= some B)
   (A': Lp G M alpha) (B': Lp G M beta) (heq: H.state= F.E2 A' B')
   (hlocalA: p alpha A→ p alpha A'∨ p beta B')
   (hlocalB: p beta B→ p alpha A'∨ p beta B') (h: F.Mn p): H.Mn p:= by
 have ha: H.state alpha= some A':= by rw [heq];exact F.CZ hab A' B'
 have hb: H.state beta= some B':= by rw [heq];exact F.E3 A' B'
 have hin (hx: p alpha A'∨ p beta B'): H.Mn p:= by
   rcases hx with hx|hx
   · exact ⟨alpha,A',ha,hx⟩
   · exact ⟨beta,B',hb,hx⟩
 obtain ⟨r,R,hR,hp⟩:= h
 by_cases hra: r= alpha
 · subst r
   cases Option.some.inj (hR.symm.trans hA)
   exact hin (hlocalA hp)
 · by_cases hrb: r= beta
   · subst r
     cases Option.some.inj (hR.symm.trans hB)
     exact hin (hlocalB hp)
   · exact ⟨r,R,by rw [heq,F.C0 A' B' r hra hrb];exact hR,hp⟩
lemma Hw (F: G8 G M) (p:∀r,Lp G M r→ Prop)
   (f:∀r,Lp G M r→ Lp G M r) (hv:∀r R,(f r R).tree.vertices= R.tree.vertices)
   (hf:∀r R,p r R→ p r (f r R)) (h: F.Mn p):(F.LU f hv).Mn p:= by
 obtain ⟨r,R,hR,hp⟩:= h
 refine ⟨r,f r R,?_,hf r R hp⟩
 change (F.state r).map (f r)= some (f r R)
 rw [hR];rfl
end Be.G8
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S: tI G M ell} {x y: Fin N} {R: y7 S x y}
namespace Bi
variable {r: Fin N} (T: Bi G M r)
lemma fJ (C: Finset (Fin N ×Fin N)) (hC:∀u v,(u,v)∈ C→ G.Adj u v)
   (e: Fin N ×Fin N) (he: T.Reaches e):(T.FX C hC).normalized.Reaches e:=
 ((T.FX C hC).u0 e).mpr
   (T.Ij _ subset_union_left e he)
lemma vN (e: Fin N ×Fin N) (he: T.Reaches e): T.normalized.Reaches e:=
 (T.u0 e).mpr he
end Bi
lemma Bb.lQ (A: Bb R) (e: Fin N ×Fin N)
   (h: S.ND.Mn (fun _ B=> B.tree.Reaches e∧ B.tree.Reaches e.swap)):
   A.Nj.ND.Mn (fun _ B=> B.tree.Reaches e∧ B.tree.Reaches e.swap):= by
 cases A with
 | single hOwner =>
   apply G8.t8 S.ND _ (fun _ B=> B.tree.Reaches e∧ B.tree.Reaches e.swap)
     R.state _ R.present rfl _ h
   intro hp
   constructor
   · apply Bi.vN
     exact R.state.tree.Ij _ subset_union_left e hp.1
   · apply Bi.vN
     exact R.state.tree.Ij _ subset_union_left e.swap hp.2
 | inactive D B hB hAT hBT hStem hTarget hInactive =>
   apply G8.t9 S.ND _ (fun _ B=> B.tree.Reaches e∧ B.tree.Reaches e.swap)
     D.distinct R.state B R.present hB _ _ rfl _ _ h
   · intro hp
     left
     constructor
     · apply Bi.fJ
       apply D.left.Ij D.JM D.BY
       simpa only [hAT] using hp.1
     · apply Bi.fJ
       apply D.left.Ij D.JM D.BY
       simpa only [hAT] using hp.2
   · intro hp
     have hc: D.right.qK:= by rw [←hBT];exact S.complete _ B hB
     have hpair:= D.lQ hc e (by simpa only [hBT] using hp.1) (by simpa only [hBT] using hp.2)
     rcases hpair with hleft|hright
     · left
       exact ⟨Bi.fJ _ _ _ _ hleft.1,
         Bi.fJ _ _ _ _ hleft.2⟩
     · right
       exact ⟨Bi.fJ _ _ _ _ hright.1,
         Bi.fJ _ _ _ _ hright.2⟩
 | active D B hB hAT hBT hStem hTarget hActive =>
   apply G8.t9 S.ND _ (fun _ B=> B.tree.Reaches e∧ B.tree.Reaches e.swap)
     D.data.distinct R.state B R.present hB _ _ rfl _ _ h
   · intro hp
     left
     constructor
     · apply Bi.fJ
       apply D.data.left.Ij _ (Classical.choice D.transfer).NL
       simpa only [hAT] using hp.1
     · apply Bi.fJ
       apply D.data.left.Ij _ (Classical.choice D.transfer).NL
       simpa only [hAT] using hp.2
   · intro hp
     have hc: D.data.right.qK:= by rw [←hBT];exact S.complete _ B hB
     have hpair:=(Classical.choice D.transfer).No hc e (by simpa only [hBT] using hp.1) (by simpa only [hBT] using hp.2)
     rcases hpair with hleft|hright
     · left
       exact ⟨Bi.fJ _ _ _ _ hleft.1,
         Bi.fJ _ _ _ _ hleft.2⟩
     · right
       exact ⟨Bi.fJ _ _ _ _ hright.1,
         Bi.fJ _ _ _ _ hright.2⟩
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
namespace Bi
variable {alpha beta: Fin N} (L: Bi G M alpha) (R: Bi G M beta)
lemma dR (C: Finset (Fin N ×Fin N))
   (hC:∀u v,(u,v)∈ C→ G.Adj u v) (hL: L.NS ⊆C) (hR: R.NS ⊆C)
   (hdis: Disjoint L.vertices R.vertices) (hNo:¬Nonempty (C3 (Mv G C) M))
   (a b: Fin N ×Fin N) (ha: L.Reaches a∨ R.Reaches a) (hb: L.Reaches b∨ R.Reaches b)
   (he:(a.2,b.2)∈ C) (hM:¬M.Adj a.2 b.2):
   ((L.FX C hC).normalized.Reaches a∧(L.FX C hC).normalized.Reaches b∧
     (a.2,b.2)∈(L.FX C hC).normalized.NS)∨
   ((R.FX C hC).normalized.Reaches a∧(R.FX C hC).normalized.Reaches b∧
     (a.2,b.2)∈(R.FX C hC).normalized.NS):= by
 have hLC (u v: Fin N) (huv:(u,v)∈ L.NS):(Mv G C).Adj u v:=⟨hC u v (hL huv),Or.inl (hL huv)⟩
 have hRC (u v: Fin N) (huv:(u,v)∈ R.NS):(Mv G C).Adj u v:=⟨hC u v (hR huv),Or.inl (hR huv)⟩
 have hEdge:(Mv G C).Adj a.2 b.2:=⟨hC _ _ he,Or.inl he⟩
 have hKeep {r: Fin N} (T: Bi G M r) (hTa: T.Reaches a) (hTb: T.Reaches b):
     (T.FX C hC).normalized.Reaches a∧(T.FX C hC).normalized.Reaches b∧
       (a.2,b.2)∈(T.FX C hC).normalized.NS:= by
   refine ⟨T.fJ C hC a hTa,T.fJ C hC b hTb,?_⟩
   apply (T.FX C hC).Cl
   exact T.i0 C hC a.2 b.2 he hM (T.yG a hTa).2 (T.yG b hTb).2
 rcases ha with ha|ha
 · rcases hb with hb|hb
   · exact Or.inl (hKeep L ha hb)
   · exact (L.cH R hdis hLC hRC hNo a b ha hb hEdge (hC _ _ he) hM).elim
 · rcases hb with hb|hb
   · exact (R.cH L hdis.symm hRC hLC hNo a b ha hb hEdge (hC _ _ he) hM).elim
   · exact Or.inr (hKeep R ha hb)
end Bi
namespace G6
variable {alpha beta: Fin N} (D: G6 G M alpha beta)
lemma HW (u v: Fin N) (he:(u,v)∈ D.KC): G.Adj u v:= by
 rcases mem_union.mp he with he|he
 · rcases mem_union.mp he with he|he
   · exact D.left.valid u v he
   · exact D.right.valid u v he
 · simp only [mem_insert,mem_singleton] at he
   rcases he with he|he
   · obtain ⟨hu,hv⟩:= Prod.mk.inj he
     rw [hu,hv];exact D.Nz
   · obtain ⟨hu,hv⟩:= Prod.mk.inj he
     rw [hu,hv];exact D.Nz.symm
lemma pY (hS: D.right.qK) (e: Fin N ×Fin N) (he: D.right.Reaches e):
   D.JM.Reaches e∨ D.remaining.Reaches e:= by
 have hmem:= D.right.mJ hS e he
 have hM:= D.right.Cv e he
 rcases (D.xJ e hM).mpr (Or.inr hmem) with hl|hr
 · exact Or.inl (D.JM.EE e hl hM)
 · exact Or.inr (D.remaining.EE e hr hM)
lemma cS (hS: D.right.qK)
   (a b: Fin N ×Fin N) (ha: D.right.Reaches a) (hb: D.right.Reaches b)
   (he:(a.2,b.2)∈ D.right.NS) (hM:¬M.Adj a.2 b.2):
   ((D.JM.FX D.KC D.HW).normalized.Reaches a∧
     (D.JM.FX D.KC D.HW).normalized.Reaches b∧
     (a.2,b.2)∈(D.JM.FX D.KC D.HW).normalized.NS)∨
   ((D.remaining.FX D.KC D.HW).normalized.Reaches a∧
     (D.remaining.FX D.KC D.HW).normalized.Reaches b∧
     (a.2,b.2)∈(D.remaining.FX D.KC D.HW).normalized.NS):= by
 exact D.JM.dR D.remaining D.KC D.HW D.En
   ((D.right.pU _).trans D.AO) D.p9 D.Ck a b
   (D.pY hS a ha) (D.pY hS b hb) (D.AO he) hM
end G6
end Be
end
noncomputable section
namespace Be.G6
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {alpha beta: Fin N}
   (D: G6 G M alpha beta)
lemma fK (hC:∀u v,(u,v)∈ D.KC→ G.Adj u v):
   (D.remaining.FX D.KC hC).normalized.vertices ⊆D.right.vertices:= by
 rw [(D.remaining.FX D.KC hC).r8,D.remaining.kK]
 exact D.right.g6 _
lemma eG (hC:∀u v,(u,v)∈ D.KC→ G.Adj u v):
   Mv G (D.remaining.FX D.KC hC).normalized.NS≤ Mv G D.right.NS:= by
 have hsub: D.remaining.vertices ⊆D.right.vertices:= D.right.g6 _
 have hx: D.NX.vertex (2*D.NX.length)∈ D.left.vertices:=
   D.left.EA D.NX D.inside (D.NX.mem_support (2*D.NX.length) le_rfl)
 have hRaw:∀u v,(u,v)∈(D.remaining.FX D.KC hC).NS→(Mv G D.right.NS).Adj u v:= by
   intro u v he
   rcases mem_union.mp he with he|he
   · exact ⟨D.remaining.valid u v he,Or.inl (D.right.pU _ he)⟩
   · obtain ⟨he,hm,hu,hv⟩:= mem_filter.mp he
     have huR:= hsub hu
     have hvR:= hsub hv
     rcases mem_union.mp he with he|he
     · rcases mem_union.mp he with he|he
       · exact (disjoint_left.mp D.disjoint (D.left.Ft u v he).1 huR).elim
       · exact ⟨D.right.valid u v he,Or.inl he⟩
     · simp only [mem_insert,mem_singleton] at he
       rcases he with he|he
       · obtain ⟨hu',hv'⟩:= Prod.mk.inj he
         rw [hu'] at huR
         exact (disjoint_left.mp D.disjoint hx huR).elim
       · obtain ⟨hu',hv'⟩:= Prod.mk.inj he
         rw [hv'] at hvR
         exact (disjoint_left.mp D.disjoint hx hvR).elim
 exact qR _ ((D.remaining.FX D.KC hC).r7 (Mv G D.right.NS) hRaw)
end Be.G6
end
noncomputable section
namespace Be.tI
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ} (S: tI G M ell)
def mapRoots (f:∀r,Lp G M r→ Lp G M r)
   (hVertices:∀r R,(f r R).tree.vertices= R.tree.vertices)
   (hLive:∀r R,S.ND.state r= some R→∀u v,(u,v)∈(f r R).tree.NS→ S.NV.Adj u v)
   (hComplete:∀r R,R.tree.qK→(f r R).tree.qK)
   (hLabels:∀r R,R.Mq ell S.labels→(f r R).Mq ell S.labels): tI G M ell:= by
 let F:= S.ND.LU f hVertices
 have hOld:∀r R,F.state r= some R→∃T,S.ND.state r= some T∧ f r T= R:= by
   intro r R hR
   change (S.ND.state r).map (f r)= some R at hR
   exact Option.map_eq_some_iff.mp hR
 exact {
   MG:= S.MG
   ND:= F
   labels:= S.labels
   Nm:= S.Nm
   NV:= S.NV
   found:= S.found
   MF:= S.MF
   HK:= S.HK
   HQ:= S.HQ
   EL:= S.EL
   DQ:= S.DQ
   Hu:= S.Hu
   DO:= by
     intro r R hR
     obtain ⟨T,hT,hTR⟩:= hOld r R hR
     rw [←hTR,hVertices]
     exact S.DO r T hT
   I9:= by
     intro r R hR
     obtain ⟨T,hT,hTR⟩:= hOld r R hR
     rw [←hTR]
     exact hLive r T hT
   Iu:= by
     intro r hf hr
     obtain ⟨R,hR⟩:= S.Iu r hf hr
     exact ⟨f r R,by change (S.ND.state r).map (f r)= some (f r R);rw [hR];rfl⟩
   labelled:= S.ND.uO f hVertices ell S.labels S.labelled hLabels
   complete:= by
     intro r R hR
     obtain ⟨T,hT,hTR⟩:= hOld r R hR
     rw [←hTR]
     exact hComplete r T (S.complete r T hT)
   positive:= S.positive
   upper:= S.upper}
def IX (limit: ℕ): tI G M ell:=
 S.mapRoots (fun _ R=> R.IX limit) (fun _ _=> rfl)
   (fun r R hR=> S.I9 r R hR) (fun _ _ h=> h) (fun _ _ h=> h)
def rC (limit: ℕ): tI G M ell:=
 S.mapRoots (fun _ R=> R.rC limit) (fun _ _=> rfl)
   (fun r R hR=> S.I9 r R hR) (fun _ _ h=> h) (fun _ _ h=> h)
def Dk: tI G M ell:=
 S.mapRoots (fun _ R=> R.zS)
   (by intro r R;unfold Lp.zS;split_ifs<;> rfl)
   (by
     intro r R hR
     unfold Lp.zS
     split_ifs<;> exact S.I9 r R hR)
   (by intro r R h;unfold Lp.zS;split_ifs<;> exact h)
   (fun _ R h=> R.eS ell S.labels h)
end Be.tI
end
noncomputable section
namespace Be.Lp
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {root: Fin N} (R: Lp G M root)
def z8 (H: SimpleGraph (Fin N)) (hHG: H≤ G): Lp G M root:= by
 let C: Finset (Fin N ×Fin N):= univ.filter (fun e=> H.Adj e.1 e.2)
 have hC:∀u v,(u,v)∈ C→ G.Adj u v:= fun u v h=> hHG (mem_filter.mp h).2
 exact {
   tree:=(R.tree.FX C hC).normalized
   active:= R.active
   inside:= fun P hP i hi=>(R.tree.FX C hC).Cl (mem_union_left _ (R.inside P hP i hi))
   NU:= R.NU
   modified:= R.modified
   extended:= R.extended}
lemma fA (H: SimpleGraph (Fin N)) (hHG: H≤ G):
   (R.z8 H hHG).tree.vertices= R.tree.vertices:= by
 exact (R.tree.FX _ _).r8.trans (R.tree.kK _ _)
lemma e8 (H: SimpleGraph (Fin N)) (hHG: H≤ G):
   (R.z8 H hHG).tree.qK:=(R.tree.FX _ _).r6
lemma e9 (H: SimpleGraph (Fin N)) (hHG: H≤ G)
   (ell: ℕ) (lab: Fin N ×Fin N→ ℕ) (hR: R.Mq ell lab):
   (R.z8 H hHG).Mq ell lab:= hR
lemma mX (H: SimpleGraph (Fin N)) (hHG: H≤ G)
   (hR:∀u v,(u,v)∈ R.tree.NS→ H.Adj u v):
   ∀u v,(u,v)∈(R.z8 H hHG).tree.NS→ H.Adj u v:= by
 let C: Finset (Fin N ×Fin N):= univ.filter (fun e=> H.Adj e.1 e.2)
 have hC:∀u v,(u,v)∈ C→ G.Adj u v:= fun u v he=> hHG (mem_filter.mp he).2
 have hTC: R.tree.NS ⊆C:= by
   intro e he
   exact mem_filter.mpr ⟨mem_univ _,hR e.1 e.2 he⟩
 exact R.tree.dS C hC hTC H (fun u v he=>(mem_filter.mp he).2)
end Be.Lp
namespace Be.tI
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ} (S: tI G M ell)
def z9: tI G M ell:=
 S.mapRoots (fun _ R=> R.z8 S.NV S.MF)
   (fun _ R=> R.fA S.NV S.MF)
   (fun r R hR=> R.mX S.NV S.MF (S.I9 r R hR))
   (fun _ R _=> R.e8 S.NV S.MF)
   (fun _ R hR=> R.e9 S.NV S.MF ell S.labels hR)
end Be.tI
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
inductive M3 (honorExtended: Bool) (x y: Fin N):
   tI G M ell→ tI G M ell→ Prop where
 | augmentation {S: tI G M ell} (R: qF S x y)
     (hflag: honorExtended= true→ R.left.extended= false):
     M3 honorExtended x y S (S.sE R)
 | extension {S: tI G M ell} (hmode: honorExtended= true)
     (R: y7 S x y) (hNo:¬S.Bd x y true) (A: Bb R):
     M3 honorExtended x y S A.Nj
 | skip {S: tI G M ell} (hNo:¬S.Bd x y honorExtended)
     (hNoExt: honorExtended= true→¬Nonempty (y7 S x y)): M3 honorExtended x y S S
inductive M2 (mode: Bool): List (Fin N ×Fin N)→
   tI G M ell→ tI G M ell→ Prop where
 | nil (S: tI G M ell): M2 mode [] S S
 | cons {x y: Fin N} {es: List (Fin N ×Fin N)} {S T U: tI G M ell}
     (step: M3 mode x y S T) (rest: M2 mode es T U): M2 mode ((x,y)::es) S U
end Be
end
noncomputable section
namespace Be.G8
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
def Df (F H: G8 G M): Prop:=
 ∀r R,H.state r= some R→ R.modified= false→
   ∃Q,F.state r= some Q∧ Q.modified= false∧ R.active= Q.active∧ R.NU= Q.NU∧ R.extended= Q.extended
def Mp (F H: G8 G M): Prop:=
 ∀r R,H.state r= some R→∃Q,F.state r= some Q∧ R.NU= Q.NU
lemma s5 (F: G8 G M): Df F F:= by
 intro r R hR hm
 exact ⟨R,hR,hm,rfl,rfl,rfl⟩
lemma FV (F: G8 G M): Mp F F:= by
 intro r R hR
 exact ⟨R,hR,rfl⟩
lemma Df.trans {F H K: G8 G M} (hFH: Df F H) (hHK: Df H K): Df F K:= by
 intro r R hR hm
 obtain ⟨Q,hQ,hQm,hRA,hRH,hRE⟩:= hHK r R hR hm
 obtain ⟨P,hP,hPm,hQA,hQH,hQE⟩:= hFH r Q hQ hQm
 exact ⟨P,hP,hPm,hRA.trans hQA,hRH.trans hQH,hRE.trans hQE⟩
lemma Mp.trans {F H K: G8 G M} (hFH: Mp F H) (hHK: Mp H K): Mp F K:= by
 intro r R hR
 obtain ⟨Q,hQ,hRH⟩:= hHK r R hR
 obtain ⟨P,hP,hQH⟩:= hFH r Q hQ
 exact ⟨P,hP,hRH.trans hQH⟩
lemma dC (F: G8 G M) (D: Finset (Fin N)): Df F (F.Jy D):= by
 intro r R hR hm
 change (if r∈ D then none else F.state r)= some R at hR
 split_ifs at hR
 exact ⟨R,hR,hm,rfl,rfl,rfl⟩
lemma nQ (F: G8 G M) (D: Finset (Fin N)): Mp F (F.Jy D):= by
 intro r R hR
 change (if r∈ D then none else F.state r)= some R at hR
 split_ifs at hR
 exact ⟨R,hR,rfl⟩
lemma cL (F H: G8 G M) {alpha: Fin N} (A: Lp G M alpha)
   (heq: H.state= Function.update F.state alpha (some A))
   (hmark: A.modified= true): Df F H:= by
 intro r R hR hm
 rw [heq] at hR
 by_cases hra: r= alpha
 · subst r
   simp only [Function.update_self,Option.some.injEq] at hR
   cases hR
   rw [hmark] at hm
   cases hm
 · rw [Function.update_of_ne hra] at hR
   exact ⟨R,hR,hm,rfl,rfl,rfl⟩
lemma kI (F H: G8 G M) {alpha: Fin N} (A A': Lp G M alpha)
   (hA: F.state alpha= some A) (heq: H.state= Function.update F.state alpha (some A'))
   (hheld: A'.NU= A.NU): Mp F H:= by
 intro r R hR
 rw [heq] at hR
 by_cases hra: r= alpha
 · subst r
   simp only [Function.update_self,Option.some.injEq] at hR
   cases hR
   exact ⟨A,hA,hheld⟩
 · rw [Function.update_of_ne hra] at hR
   exact ⟨R,hR,rfl⟩
lemma cM (F H: G8 G M) {alpha beta: Fin N} (hab: alpha≠ beta)
   (A: Lp G M alpha) (B: Lp G M beta)
   (hA: F.state alpha= some A) (hB: F.state beta= some B)
   (A': Lp G M alpha) (B': Lp G M beta)
   (heq: H.state= F.E2 A' B') (hmark: A'.modified= true)
   (hBback: B'.modified= false→ B.modified= false∧ B'.active= B.active∧ B'.NU= B.NU∧ B'.extended= B.extended): Df F H:= by
 intro r R hR hm
 rw [heq] at hR
 by_cases hra: r= alpha
 · subst r
   rw [F.CZ hab] at hR
   cases Option.some.inj hR
   rw [hmark] at hm
   cases hm
 · by_cases hrb: r= beta
   · subst r
     rw [F.E3] at hR
     cases Option.some.inj hR
     obtain ⟨hBm,hBA,hBH,hBE⟩:= hBback hm
     exact ⟨B,hB,hBm,hBA,hBH,hBE⟩
   · rw [F.C0 A' B' r hra hrb] at hR
     exact ⟨R,hR,hm,rfl,rfl,rfl⟩
lemma kJ (F H: G8 G M) {alpha beta: Fin N} (hab: alpha≠ beta)
   (A: Lp G M alpha) (B: Lp G M beta)
   (hA: F.state alpha= some A) (hB: F.state beta= some B)
   (A': Lp G M alpha) (B': Lp G M beta)
   (heq: H.state= F.E2 A' B') (hheldA: A'.NU= A.NU) (hheldB: B'.NU= B.NU): Mp F H:= by
 intro r R hR
 rw [heq] at hR
 by_cases hra: r= alpha
 · subst r
   rw [F.CZ hab] at hR
   cases Option.some.inj hR
   exact ⟨A,hA,hheldA⟩
 · by_cases hrb: r= beta
   · subst r
     rw [F.E3] at hR
     cases Option.some.inj hR
     exact ⟨B,hB,hheldB⟩
   · rw [F.C0 A' B' r hra hrb] at hR
     exact ⟨R,hR,rfl⟩
end Be.G8
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S: tI G M ell} {x y: Fin N}
lemma Bb.CX {R: y7 S x y} (A: Bb R):
   G8.Df S.ND A.Nj.ND:= by
 cases A with
 | single hOwner =>
   apply G8.cL S.ND _ _ rfl
   rfl
 | inactive D B hB hAT hBT hStem hTarget hInactive =>
   apply G8.cM S.ND _ D.distinct R.state B R.present hB _ _ rfl
   · rfl
   · intro h
     exact ⟨h,rfl,rfl,rfl⟩
 | active D B hB hAT hBT hStem hTarget hActive =>
   apply G8.cM S.ND _ D.data.distinct R.state B R.present hB _ _ rfl
   · rfl
   · intro h
     change true= false at h
     cases h
lemma Bb.LJ {R: y7 S x y} (A: Bb R):
   G8.Mp S.ND A.Nj.ND:= by
 cases A with
 | single hOwner =>
   apply G8.kI S.ND _ R.state _ R.present rfl
   rfl
 | inactive D B hB hAT hBT hStem hTarget hInactive =>
   apply G8.kJ S.ND _ D.distinct R.state B R.present hB _ _ rfl<;> rfl
 | active D B hB hAT hBT hStem hTarget hActive =>
   apply G8.kJ S.ND _ D.data.distinct R.state B R.present hB _ _ rfl<;> rfl
lemma M3.CX {mode: Bool} {T: tI G M ell} (h: M3 mode x y S T):
   G8.Df S.ND T.ND:= by
 cases h with
 | augmentation R hflag => apply G8.dC
 | extension hmode R hNo A => exact A.CX
 | skip hNo hNoExt => exact G8.s5 S.ND
lemma M3.LJ {mode: Bool} {T: tI G M ell} (h: M3 mode x y S T):
   G8.Mp S.ND T.ND:= by
 cases h with
 | augmentation R hflag => apply G8.nQ
 | extension hmode R hNo A => exact A.LJ
 | skip hNo hNoExt => exact G8.FV S.ND
lemma M2.CX {mode: Bool} {es: List (Fin N ×Fin N)} {T: tI G M ell}
   (h: M2 mode es S T): G8.Df S.ND T.ND:= by
 induction h with
 | nil S => exact G8.s5 S.ND
 | cons step rest ih => exact step.CX.trans ih
lemma M2.LJ {mode: Bool} {es: List (Fin N ×Fin N)} {T: tI G M ell}
   (h: M2 mode es S T): G8.Mp S.ND T.ND:= by
 induction h with
 | nil S => exact G8.FV S.ND
 | cons step rest ih => exact step.LJ.trans ih
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
lemma k8 {root: Fin N} (P: v9 G M root) (lab: Fin N ×Fin N→ ℕ)
   (a: Fin N ×Fin N) (hstrict: P.Nl lab a< lab a):
   ∃i,i< P.length∧ P.KA i= a∧ P.Nl lab a= i+1:= by
 have hex:∃i,i< P.length∧ P.KA i= a:= by
   by_contra hnot
   simp only [v9.Nl,dif_neg hnot] at hstrict
   omega
 obtain ⟨i,hi,hia⟩:= hex
 have href:= P.KX lab i hi
 rw [hia] at href
 have hbound: i+1< lab a:= by omega
 exact ⟨i,hi,hia,href.trans (min_eq_right hbound.le)⟩
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S: tI G M ell} {x y: Fin N}
namespace Bb
variable {R: y7 S x y}
def Nf (A: Bb R): v9 G M R.root:= by
 cases A with
 | single hOwner =>
   exact R.NX.Fq y R.NW (S.MF R.Do)
     (S.MG.1 R.matched) R.y1 R.matched R.Kq R.Kp
 | inactive D B hB hAT hBT hStem hTarget hInactive => exact D.K6
 | active D B hB hAT hBT hStem hTarget hActive => exact D.path
lemma LO (A: Bb R): A.Nj.labels= A.Nf.Nl S.labels:= by
 cases A<;> rfl
lemma Jj (A: Bb R):∀a,A.Nj.labels a≤ S.labels a:= by
 rw [A.LO]
 exact A.Nf.Ik S.labels
lemma EG (A: Bb R):∃Q,
   A.Nj.ND.state R.root= some Q∧ Q.active= some A.Nf∧
     Q.modified= true∧ Q.extended= true∧ Q.NU= R.state.NU:= by
 cases A with
 | single hOwner =>
   dsimp only [Nj,tI.Kg,tI.JC,G8.K0]
   rw [Function.update_self]
   exact ⟨_,rfl,rfl,rfl,rfl,rfl⟩
 | inactive D B hB hAT hBT hStem hTarget hInactive =>
   dsimp only [Nj,tI.AE,tI.JB,G8.K1]
   rw [S.ND.CZ D.distinct]
   exact ⟨_,rfl,rfl,rfl,rfl,rfl⟩
 | active D B hB hAT hBT hStem hTarget hActive =>
   dsimp only [Nj,tI.Ew,tI.JB,G8.K1]
   rw [S.ND.CZ D.data.distinct]
   exact ⟨_,rfl,rfl,rfl,rfl,rfl⟩
lemma CS (A: Bb R): A.Nf.KA R.NX.length=(y,R.NW):= by
 cases A with
 | single hOwner => exact R.NX.tM y R.NW (S.MF R.Do) (S.MG.1 R.matched) R.y1 R.matched R.Kq R.Kp
 | inactive D B hB hAT hBT hStem hTarget hInactive =>
   change D.K6.KA R.NX.length=(y,R.NW)
   rw [←hStem,D.yT,hTarget]
 | active D B hB hAT hBT hStem hTarget hActive =>
   change D.path.KA R.NX.length=(y,R.NW)
   rw [←hStem]
   have ht:= D.data.NX.fQ D.Ng D.index D.positive D.bound D.separation D.Nz D.zV D.data.NX.length le_rfl
   change D.path.KA D.data.NX.length= _ at ht
   simpa only [Nat.sub_self,zero_add,D.target,hTarget] using ht
lemma Iz (A: Bb R): R.NX.M4 A.Nf:= by
 cases A with
 | single hOwner => exact R.NX.l3 y R.NW (S.MF R.Do) (S.MG.1 R.matched) R.y1 R.matched R.Kq R.Kp
 | inactive D B hB hAT hBT hStem hTarget hInactive =>
   rw [←hStem]
   exact D.NX.l3 D.target.1 D.target.2 D.Nz (D.MG.1 D.EV) D.zV D.EV D.yX D.yW
 | active D B hB hAT hBT hStem hTarget hActive =>
   rw [←hStem]
   exact D.data.NX.jQ D.Ng D.index D.positive D.bound D.separation D.Nz D.zV
lemma yY (A: Bb R): R.NX.length< A.Nf.length:= by
 cases A with
 | single hOwner => change R.NX.length< R.NX.length+1;omega
 | inactive D B hB hAT hBT hStem hTarget hInactive =>
   change R.NX.length< D.NX.length+1
   rw [hStem];omega
 | active D B hB hAT hBT hStem hTarget hActive =>
   change R.NX.length< D.path.length
   rw [←hStem]
   have hb:= D.bound
   have hp:= D.positive
   change D.data.NX.length< D.data.NX.length+(D.Ng.length+1-D.index)
   omega
lemma GS (A: Bb R): A.Nj.labels (y,R.NW)< S.labels (y,R.NW):= by
 rw [A.LO,←A.CS]
 apply A.Nf.EI S.labels _ A.yY
 rw [A.CS]
 exact R.My
end Bb
lemma M3.Jj {mode: Bool} {T: tI G M ell} (h: M3 mode x y S T):
   ∀a,T.labels a≤ S.labels a:= by
 cases h with
 | augmentation R hflag => exact fun _=> le_rfl
 | extension hmode R hNo A => exact A.Jj
 | skip hNo hNoExt => exact fun _=> le_rfl
lemma M2.Jj {mode: Bool} {es: List (Fin N ×Fin N)} {T: tI G M ell}
   (h: M2 mode es S T):∀a,T.labels a≤ S.labels a:= by
 induction h with
 | nil S => exact fun _=> le_rfl
 | cons step rest ih => exact fun a=>(ih a).trans (step.Jj a)
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell} {x y: Fin N}
lemma M3.kT {mode: Bool} (h: M3 mode x y S T)
   {r: Fin N} (Q: Lp G M r) (hQ: T.ND.state r= some Q) (hmod: Q.modified= false)
   (e: Fin N ×Fin N) (he: e.1∈ Q.tree.vertices): T.labels e= S.labels e:= by
 cases h with
 | augmentation R hflag => rfl
 | skip hNo hNoExt => rfl
 | extension hmode R hNo A =>
   by_contra hneq
   have hstrict: A.Nj.labels e< S.labels e:= lt_of_le_of_ne (A.Jj e) hneq
   rw [A.LO] at hstrict
   obtain ⟨i,hi,hie,hnew⟩:= k8 A.Nf S.labels e hstrict
   obtain ⟨B,hB,hactive,hBmod,hBext,hBheld⟩:= A.EG
   have hmem:= B.tree.EA A.Nf (B.inside A.Nf hactive) (A.Nf.mem_support (2*i+1) (by omega))
   change (A.Nf.KA i).1∈ B.tree.vertices at hmem
   rw [hie] at hmem
   have heq:= A.Nj.ND.BE r R.root e.1 ⟨Q,hQ,he⟩ ⟨B,hB,hmem⟩
   have hex:∃Q,A.Nj.ND.state r= some Q∧ Q.modified= false:=⟨Q,hQ,hmod⟩
   rw [heq] at hex
   obtain ⟨Q,hQ,hm⟩:= hex
   cases Option.some.inj (hQ.symm.trans hB)
   rw [hBmod] at hm
   cases hm
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
namespace G8
def oA (F H: G8 G M): Prop:=
 ∀r R,H.state r= some R→ R.modified= false→∃Q,F.state r= some Q∧ Q.modified= false∧
   R.tree.vertices ⊆Q.tree.vertices∧ Mv G R.tree.NS≤ Mv G Q.tree.NS∧
   (∀u v,(u,v)∈ Q.tree.NS→ u∈ R.tree.vertices→ v∈ R.tree.vertices→¬M.Adj u v→(u,v)∈ R.tree.NS)
lemma fU (F: G8 G M): oA F F:= by
 intro r R hR hm
 exact ⟨R,hR,hm,subset_refl _,le_rfl,fun _ _ he _ _ _=> he⟩
lemma oA.trans {F H K: G8 G M} (hFH: oA F H)
   (hHK: oA H K): oA F K:= by
 intro r R hR hm
 obtain ⟨Q,hQ,hQm,hvRQ,hgRQ,hcRQ⟩:= hHK r R hR hm
 obtain ⟨P,hP,hPm,hvQP,hgQP,hcQP⟩:= hFH r Q hQ hQm
 refine ⟨P,hP,hPm,hvRQ.trans hvQP,hgRQ.trans hgQP,?_⟩
 intro u v he hu hv hm
 exact hcRQ u v (hcQP u v he (hvRQ hu) (hvRQ hv) hm) hu hv hm
lemma dL (F H: G8 G M) {alpha: Fin N} (A: Lp G M alpha)
   (heq: H.state= Function.update F.state alpha (some A)) (hmark: A.modified= true): oA F H:= by
 intro r R hR hm
 rw [heq] at hR
 by_cases hra: r= alpha
 · subst r
   rw [Function.update_self] at hR
   cases Option.some.inj hR
   rw [hmark] at hm
   cases hm
 · rw [Function.update_of_ne hra] at hR
   exact ⟨R,hR,hm,subset_refl _,le_rfl,fun _ _ he _ _ _=> he⟩
lemma dM (F H: G8 G M) {alpha beta: Fin N} (hab: alpha≠ beta)
   (B: Lp G M beta) (hB: F.state beta= some B)
   (A': Lp G M alpha) (B': Lp G M beta) (heq: H.state= F.E2 A' B')
   (hmark: A'.modified= true)
   (hBback: B'.modified= false→ B.modified= false∧ B'.tree.vertices ⊆B.tree.vertices∧
     Mv G B'.tree.NS≤ Mv G B.tree.NS∧
     (∀u v,(u,v)∈ B.tree.NS→ u∈ B'.tree.vertices→ v∈ B'.tree.vertices→¬M.Adj u v→(u,v)∈ B'.tree.NS)): oA F H:= by
 intro r R hR hm
 rw [heq] at hR
 by_cases hra: r= alpha
 · subst r
   rw [F.CZ hab] at hR
   cases Option.some.inj hR
   rw [hmark] at hm
   cases hm
 · by_cases hrb: r= beta
   · subst r
     rw [F.E3] at hR
     cases Option.some.inj hR
     obtain ⟨hBm,hv,hg,hc⟩:= hBback hm
     exact ⟨B,hB,hBm,hv,hg,hc⟩
   · rw [F.C0 A' B' r hra hrb] at hR
     exact ⟨R,hR,hm,subset_refl _,le_rfl,fun _ _ he _ _ _=> he⟩
end G8
variable {ell: ℕ} {S T: tI G M ell} {x y: Fin N}
lemma Bb.lY {R: y7 S x y} (A: Bb R):
   G8.oA S.ND A.Nj.ND:= by
 cases A with
 | single hOwner =>
   exact G8.dL S.ND _ _ rfl rfl
 | inactive D B hB hAT hBT hStem hTarget hInactive =>
   apply G8.dM S.ND _ D.distinct B hB _ _ rfl rfl
   intro h
   refine ⟨h,?_,?_,?_⟩
   · rw [hBT]
     exact D.fK D.HW
   · rw [hBT]
     exact D.eG D.HW
   · intro u v he hu hv hm
     change u∈(D.remaining.FX D.KC D.HW).normalized.vertices at hu
     change v∈(D.remaining.FX D.KC D.HW).normalized.vertices at hv
     rw [(D.remaining.FX D.KC D.HW).r8,D.remaining.kK] at hu hv
     apply (D.remaining.FX D.KC D.HW).Cl
     exact D.remaining.i0 D.KC D.HW u v
       (D.AO (by rw [←hBT];exact he)) hm hu hv
 | active D B hB hAT hBT hStem hTarget hActive =>
   apply G8.dM S.ND _ D.data.distinct B hB _ _ rfl rfl
   intro h
   change true= false at h
   cases h
lemma M3.lY {mode: Bool} (h: M3 mode x y S T):
   G8.oA S.ND T.ND:= by
 cases h with
 | augmentation A hflag =>
   intro r R hR hm
   change (if r∈({A.ME,A.L7}:Finset (Fin N)) then none else S.ND.state r)= some R at hR
   split_ifs at hR
   exact ⟨R,hR,hm,subset_refl _,le_rfl,fun _ _ he _ _ _=> he⟩
 | extension hmode R hNo A => exact A.lY
 | skip hNo hNoExt => exact G8.fU S.ND
lemma M2.lY {mode: Bool} {es: List (Fin N ×Fin N)} (h: M2 mode es S T):
   G8.oA S.ND T.ND:= by
 induction h with
 | nil S => exact G8.fU S.ND
 | cons step rest ih => exact step.lY.trans ih
lemma M2.i6 {mode: Bool} {es: List (Fin N ×Fin N)} (h: M2 mode es S T):
   ∀r Q,T.ND.state r= some Q→ Q.modified= false→
     ∀e: Fin N ×Fin N,e.1∈ Q.tree.vertices→ T.labels e= S.labels e:= by
 induction h with
 | nil S => intros;rfl
 | cons step rest ih =>
   intro r Q hQ hm e he
   obtain ⟨B,hB,hBm,hv,hg,hc⟩:= rest.lY r Q hQ hm
   exact (ih r Q hQ hm e he).trans (step.kT B hB hBm e (hv he))
end Be
end
noncomputable section
namespace Be.C2
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {alpha beta: Fin N}
   (D: C2 G M alpha beta)
lemma pY (hS: D.data.right.qK) (e: Fin N ×Fin N)
   (he: D.data.right.Reaches e):
   (Classical.choice D.transfer).left.Reaches e∨(Classical.choice D.transfer).right.Reaches e:= by
 have hmem:= D.data.right.mJ hS e he
 have hM:= D.data.right.Cv e he
 rcases ((Classical.choice D.transfer).matched e hM).mpr (Or.inr hmem) with hl|hr
 · exact Or.inl ((Classical.choice D.transfer).left.EE e hl hM)
 · exact Or.inr ((Classical.choice D.transfer).right.EE e hr hM)
lemma cS (hS: D.data.right.qK)
   (a b: Fin N ×Fin N) (ha: D.data.right.Reaches a) (hb: D.data.right.Reaches b)
   (he:(a.2,b.2)∈ D.data.right.NS) (hM:¬M.Adj a.2 b.2):
   (((Classical.choice D.transfer).left.FX D.data.KC D.data.HW).normalized.Reaches a∧
     ((Classical.choice D.transfer).left.FX D.data.KC D.data.HW).normalized.Reaches b∧
     (a.2,b.2)∈((Classical.choice D.transfer).left.FX D.data.KC D.data.HW).normalized.NS)∨
   (((Classical.choice D.transfer).right.FX D.data.KC D.data.HW).normalized.Reaches a∧
     ((Classical.choice D.transfer).right.FX D.data.KC D.data.HW).normalized.Reaches b∧
     (a.2,b.2)∈((Classical.choice D.transfer).right.FX D.data.KC D.data.HW).normalized.NS):= by
 exact (Classical.choice D.transfer).left.dR (Classical.choice D.transfer).right D.data.KC
   D.data.HW (Classical.choice D.transfer).Jl (Classical.choice D.transfer).Is
   (Classical.choice D.transfer).disjoint D.data.Ck a b
   (D.pY hS a ha) (D.pY hS b hb) (D.data.AO he) hM
end Be.C2
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S: tI G M ell} {x y: Fin N} {R: y7 S x y}
namespace Bi
variable {r: Fin N} (T: Bi G M r)
def Mo (a b: Fin N ×Fin N): Prop:= T.Reaches a∧ T.Reaches b∧(a.2,b.2)∈ T.NS
lemma FT (U: Bi G M r) (hTU: T.NS ⊆U.NS)
   (a b: Fin N ×Fin N) (h: T.Mo a b): U.Mo a b:=
 ⟨T.Ij U hTU a h.1,T.Ij U hTU b h.2.1,hTU h.2.2⟩
lemma q8 (a b: Fin N ×Fin N) (h: T.Mo a b): T.normalized.Mo a b:=
 ⟨T.vN a h.1,T.vN b h.2.1,T.Cl h.2.2⟩
lemma dZ (C: Finset (Fin N ×Fin N)) (hC:∀u v,(u,v)∈ C→ G.Adj u v)
   (a b: Fin N ×Fin N) (h: T.Mo a b):(T.FX C hC).normalized.Mo a b:=
 (T.FX C hC).q8 a b (T.FT (T.FX C hC) subset_union_left a b h)
end Bi
lemma Bb.q9 (A: Bb R) (a b: Fin N ×Fin N)
   (hM:¬M.Adj a.2 b.2) (h: S.ND.Mn (fun _ B=> B.tree.Mo a b)):
   A.Nj.ND.Mn (fun _ B=> B.tree.Mo a b):= by
 cases A with
 | single hOwner =>
   apply G8.t8 S.ND _ (fun _ B=> B.tree.Mo a b) R.state _ R.present rfl _ h
   intro hp
   apply Bi.q8
   exact R.state.tree.FT _ subset_union_left a b hp
 | inactive D B hB hAT hBT hStem hTarget hInactive =>
   apply G8.t9 S.ND _ (fun _ B=> B.tree.Mo a b)
     D.distinct R.state B R.present hB _ _ rfl _ _ h
   · intro hp
     left
     apply Bi.dZ
     apply D.left.FT D.JM D.BY a b
     simpa only [hAT] using hp
   · intro hp
     have hc: D.right.qK:= by rw [←hBT];exact S.complete _ B hB
     have hp': D.right.Mo a b:= by simpa only [hBT] using hp
     exact D.cS hc a b hp'.1 hp'.2.1 hp'.2.2 hM
 | active D B hB hAT hBT hStem hTarget hActive =>
   apply G8.t9 S.ND _ (fun _ B=> B.tree.Mo a b)
     D.data.distinct R.state B R.present hB _ _ rfl _ _ h
   · intro hp
     left
     apply Bi.dZ
     apply D.data.left.FT _ (Classical.choice D.transfer).NL a b
     simpa only [hAT] using hp
   · intro hp
     have hc: D.data.right.qK:= by rw [←hBT];exact S.complete _ B hB
     have hp': D.data.right.Mo a b:= by simpa only [hBT] using hp
     exact D.cS hc a b hp'.1 hp'.2.1 hp'.2.2 hM
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
namespace v9
variable {r: Fin N} (P: v9 G M r)
def E8 (E: Finset (Fin N ×Fin N)) (i: ℕ): Prop:=
 ∀j,j≤ i→ P.KA j∉ E
lemma mB {Q: v9 G M r} (hPQ: P.M4 Q)
   (E: Finset (Fin N ×Fin N)) (i: ℕ) (hi: i< P.length) (havoid: P.E8 E i):
   Q.E8 E i:= by
 intro j hj
 have he: Q.KA j= P.KA j:= Prod.ext (hPQ.2 (2*j+1) (by omega)) (hPQ.2 (2*j+2) (by omega))
 rw [he]
 exact havoid j hj
end v9
namespace C2
variable {alpha beta: Fin N} (D: C2 G M alpha beta)
lemma fR (ell: ℕ) (lab: Fin N ×Fin N→ ℕ)
   (hQ: D.Ng.Mq ell lab) (heligible: D.data.NX.length+1< lab D.data.target)
   (i: ℕ) (hi0: D.index-1≤ i) (hi: i< D.Ng.length):
   ∃n,n= D.data.NX.length+(i+1-D.index)∧ n< D.path.length∧ n< i∧ D.path.KA n= D.Ng.KA i:= by
 let n:= D.data.NX.length+(i+1-D.index)
 have hp:= D.positive
 have hb:= D.bound
 have hfirst:= hQ.2 (D.index-1) (by omega)
 change lab (D.Ng.KA (D.index-1))≤ D.index-1+1 at hfirst
 rw [D.target] at hfirst
 have hn: n< D.path.length:= by
   change n< D.data.NX.length+(D.Ng.length+1-D.index)
   dsimp [n];omega
 have hpos: D.data.NX.length≤ n:= by dsimp [n];omega
 have he:= D.data.NX.fQ D.Ng D.index D.positive D.bound D.separation D.Nz D.zV n hpos
 change D.path.KA n= _ at he
 have hidx: n-D.data.NX.length+D.index-1= i:= by dsimp [n];omega
 rw [hidx] at he
 exact ⟨n,rfl,hn,by dsimp [n];omega,he⟩
lemma jS (E: Finset (Fin N ×Fin N))
   (hE:∀e∈ E,e.1∈ D.data.right.vertices)
   (i: ℕ) (hi0: D.index-1≤ i) (hi: i< D.Ng.length)
   (havoid: D.Ng.E8 E i):
   D.path.E8 E (D.data.NX.length+(i+1-D.index)):= by
 intro j hj heE
 have hp:= D.positive
 have hb:= D.bound
 by_cases hjold: j< D.data.NX.length
 · have he:= D.data.NX.fP D.Ng D.index D.positive D.bound D.separation D.Nz D.zV j hjold
   change D.path.KA j= D.data.NX.KA j at he
   rw [he] at heE
   have hleft:(D.data.NX.KA j).1∈ D.data.left.vertices:=
     D.data.left.EA D.data.NX D.data.inside (D.data.NX.mem_support (2*j+1) (by omega))
   exact disjoint_left.mp D.data.disjoint hleft (hE _ heE)
 · have he:= D.data.NX.fQ D.Ng D.index D.positive D.bound D.separation D.Nz D.zV j (by omega)
   change D.path.KA j= _ at he
   rw [he] at heE
   exact havoid (j-D.data.NX.length+D.index-1) (by omega) heE
end C2
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
namespace Lp
variable {r: Fin N}
def Ny (A: Lp G M r) (e: Fin N ×Fin N) (k: ℕ) (E: Finset (Fin N ×Fin N)): Prop:=
 ∃P i,A.active= some P∧ i< P.length∧ i≤ k∧ P.KA i= e∧ P.E8 E i
lemma CU (A: Lp G M r) {e: Fin N ×Fin N} {k: ℕ} {E: Finset (Fin N ×Fin N)}
   (h: A.Ny e k E): e.1∈ A.tree.vertices:= by
 obtain ⟨P,i,hP,hi,hik,hie,havoid⟩:= h
 have hm:= A.tree.EA P (A.inside P hP) (P.mem_support (2*i+1) (by omega))
 change (P.KA i).1∈ A.tree.vertices at hm
 rwa [hie] at hm
lemma v1 (A B: Lp G M r) (heq: B.active= A.active)
   {e: Fin N ×Fin N} {k: ℕ} {E: Finset (Fin N ×Fin N)} (h: A.Ny e k E): B.Ny e k E:= by
 obtain ⟨P,i,hP,hi,hik,hie,havoid⟩:= h
 exact ⟨P,i,heq.trans hP,hi,hik,hie,havoid⟩
lemma EY (A B: Lp G M r) (P Q: v9 G M r)
   (hP: A.active= some P) (hQ: B.active= some Q) (hext: P.M4 Q)
   {e: Fin N ×Fin N} {k: ℕ} {E: Finset (Fin N ×Fin N)} (h: A.Ny e k E): B.Ny e k E:= by
 obtain ⟨R,i,hR,hi,hik,hie,havoid⟩:= h
 cases Option.some.inj (hR.symm.trans hP)
 have hl:= hext.1
 have he: Q.KA i= P.KA i:= Prod.ext (hext.2 (2*i+1) (by omega)) (hext.2 (2*i+2) (by omega))
 exact ⟨Q,i,hQ,by omega,hik,he.trans hie,P.mB hext E i hi havoid⟩
end Lp
namespace G8
def Ny (F: G8 G M) (e: Fin N ×Fin N) (k: ℕ) (E: Finset (Fin N ×Fin N)): Prop:=
 ∃r R,F.state r= some R∧ R.Ny e k E
lemma A2 (F H: G8 G M) {alpha: Fin N} (A A': Lp G M alpha)
   (hA: F.state alpha= some A) (heq: H.state= Function.update F.state alpha (some A'))
   (e: Fin N ×Fin N) (k: ℕ) (E: Finset (Fin N ×Fin N))
   (hlocal: A.Ny e k E→ A'.Ny e k E) (h: F.Ny e k E): H.Ny e k E:= by
 obtain ⟨r,R,hR,htrack⟩:= h
 by_cases hra: r= alpha
 · subst r
   cases Option.some.inj (hR.symm.trans hA)
   exact ⟨alpha,A',by rw [heq];exact Function.update_self _ _ _,hlocal htrack⟩
 · exact ⟨r,R,by rw [heq,Function.update_of_ne hra];exact hR,htrack⟩
lemma A3 (F H: G8 G M) {alpha beta: Fin N} (hab: alpha≠ beta)
   (A: Lp G M alpha) (B: Lp G M beta)
   (hA: F.state alpha= some A) (hB: F.state beta= some B)
   (A': Lp G M alpha) (B': Lp G M beta) (heq: H.state= F.E2 A' B')
   (e: Fin N ×Fin N) (k: ℕ) (E: Finset (Fin N ×Fin N))
   (hlocalA: A.Ny e k E→ A'.Ny e k E∨ B'.Ny e k E)
   (hlocalB: B.Ny e k E→ A'.Ny e k E∨ B'.Ny e k E)
   (h: F.Ny e k E): H.Ny e k E:= by
 have ha: H.state alpha= some A':= by rw [heq];exact F.CZ hab A' B'
 have hb: H.state beta= some B':= by rw [heq];exact F.E3 A' B'
 have hin (hx: A'.Ny e k E∨ B'.Ny e k E): H.Ny e k E:= by
   rcases hx with hx|hx
   · exact ⟨alpha,A',ha,hx⟩
   · exact ⟨beta,B',hb,hx⟩
 obtain ⟨r,R,hR,htrack⟩:= h
 by_cases hra: r= alpha
 · subst r
   cases Option.some.inj (hR.symm.trans hA)
   exact hin (hlocalA htrack)
 · by_cases hrb: r= beta
   · subst r
     cases Option.some.inj (hR.symm.trans hB)
     exact hin (hlocalB htrack)
   · exact ⟨r,R,by rw [heq,F.C0 A' B' r hra hrb];exact hR,htrack⟩
lemma Lc (F: G8 G M) (f:∀r,Lp G M r→ Lp G M r)
   (hv:∀r R,(f r R).tree.vertices= R.tree.vertices)
   (e: Fin N ×Fin N) (k: ℕ) (E: Finset (Fin N ×Fin N))
   (hf:∀r R,R.Ny e k E→(f r R).Ny e k E)
   (h: F.Ny e k E):(F.LU f hv).Ny e k E:= by
 obtain ⟨r,R,hR,htrack⟩:= h
 refine ⟨r,f r R,?_,hf r R htrack⟩
 change (F.state r).map (f r)= some (f r R)
 rw [hR]
 rfl
end G8
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S: tI G M ell} {x y: Fin N} {R: y7 S x y}
lemma Bb.A1 (A: Bb R) (e: Fin N ×Fin N) (k: ℕ)
   (E: Finset (Fin N ×Fin N))
   (htogether:∀r B,S.ND.state r= some B→ e.1∈ B.tree.vertices→∀f∈ E,f.1∈ B.tree.vertices)
   (htrack: S.ND.Ny e k E): A.Nj.ND.Ny e k E:= by
 cases A with
 | single hOwner =>
   apply G8.A2 S.ND _ R.state _ R.present rfl e k E _ htrack
   intro h
   exact Lp.EY R.state _ R.J5 (Bb.single hOwner).Nf R.Lq rfl
     (R.J5.FP R.DL (Bb.single hOwner).Iz) h
 | inactive D B hB hAT hBT hStem hTarget hInactive =>
   apply G8.A3 S.ND _ D.distinct R.state B R.present hB _ _ rfl e k E _ _ htrack
   · intro h
     left
     exact Lp.EY R.state _ R.J5 (Bb.inactive D B hB hAT hBT hStem hTarget hInactive).Nf R.Lq rfl
       (R.J5.FP R.DL (Bb.inactive D B hB hAT hBT hStem hTarget hInactive).Iz) h
   · intro h
     right
     exact Lp.v1 B _ rfl h
 | active D B hB hAT hBT hStem hTarget hActive =>
   apply G8.A3 S.ND _ D.data.distinct R.state B R.present hB _ _ rfl e k E _ _ htrack
   · intro h
     left
     exact Lp.EY R.state _ R.J5 (Bb.active D B hB hAT hBT hStem hTarget hActive).Nf R.Lq rfl
       (R.J5.FP R.DL (Bb.active D B hB hAT hBT hStem hTarget hActive).Iz) h
   · intro h
     have hE:= htogether _ B hB (B.CU h)
     rw [hBT] at hE
     obtain ⟨Q,i,hQ,hi,hik,hie,havoid⟩:= h
     have hQP: Q= D.Ng:= Option.some.inj (hQ.symm.trans hActive)
     subst Q
     by_cases hir: i< D.index-1
     · right
       refine ⟨D.Ng.take (D.index-1) (by have hb:=D.bound;omega),i,rfl,hir,hik,hie,havoid⟩
     · left
       have heligible: D.data.NX.length+1< S.labels D.data.target:= by rw [hStem,hTarget];exact R.My
       obtain ⟨n,hn,hnlen,hni,hnew⟩:= D.fR ell S.labels
         (S.labelled _ B hB D.Ng hActive) heligible i (by omega) hi
       refine ⟨D.path,n,rfl,hnlen,by omega,hnew.trans hie,?_⟩
       rw [hn]
       exact D.jS E hE i (by omega) hi havoid
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell} {x y: Fin N}
lemma M3.A1 {mode: Bool} (h: M3 mode x y S T)
   (e: Fin N ×Fin N) (k: ℕ) (E: Finset (Fin N ×Fin N))
   (htogether:∀r B,S.ND.state r= some B→ e.1∈ B.tree.vertices→∀f∈ E,f.1∈ B.tree.vertices)
   (halive: e.1∉ T.Nm) (htrack: S.ND.Ny e k E): T.ND.Ny e k E:= by
 cases h with
 | augmentation A hflag =>
   obtain ⟨r,R,hR,hrtrack⟩:= htrack
   by_cases hra: r= A.ME
   · subst r
     have hRA: R= A.left:= Option.some.inj (hR.symm.trans A.HJ)
     subst R
     exact (halive (mem_union_right _ (mem_union_left _ (A.left.CU hrtrack)))).elim
   · by_cases hrb: r= A.L7
     · subst r
       have hRB: R= A.right:= Option.some.inj (hR.symm.trans A.GE)
       subst R
       exact (halive (mem_union_right _ (mem_union_right _ (A.right.CU hrtrack)))).elim
     · refine ⟨r,R,?_,hrtrack⟩
       change (if r∈({A.ME,A.L7}:Finset (Fin N)) then none else S.ND.state r)= some R
       simp only [mem_insert,mem_singleton,hra,hrb,or_self,if_false]
       exact hR
 | extension hmode R hNo action => exact action.A1 e k E htogether htrack
 | skip hNo hNoExt => exact htrack
namespace Lp
variable {r: Fin N}
def II (A: Lp G M r) (e: Fin N ×Fin N) (k: ℕ) (E: Finset (Fin N ×Fin N)): Prop:=
 ∃P i,A.active= some P∧ i< P.length∧ i≤ k∧ P.KA i= e∧
   P.E8 E i∧ i+1= P.length∧ A.NU= false∧ A.modified= false
lemma h8 (A: Lp G M r) (e: Fin N ×Fin N) (k: ℕ)
   (E: Finset (Fin N ×Fin N)) (h: A.Ny e k E):
   A.zS.Ny e k E∨ A.II e k E:= by
 by_cases hflag:(A.NU|| A.modified)= true
 · left
   simpa only [zS,if_pos hflag] using h
 · have hheld: A.NU= false:= by cases hh: A.NU<;> simp_all
   have hmodified: A.modified= false:= by cases hm: A.modified<;> simp_all
   obtain ⟨P,i,hP,hi,hik,hie,havoid⟩:= h
   have hpos: 0< P.length:= by omega
   by_cases hi': i< P.length-1
   · left
     refine ⟨P.take (P.length-1) (by omega),i,?_,hi',hik,hie,havoid⟩
     simp only [zS,if_neg hflag,backtrack,hP,Option.bind_some,dif_pos hpos]
   · right
     exact ⟨P,i,hP,hi,hik,hie,havoid,by omega,hheld,hmodified⟩
end Lp
end Be
end
noncomputable section
namespace Be
variable {N: ℕ}
def Ke (G: SimpleGraph (Fin N)) (E: Finset (Sym2 (Fin N))): SimpleGraph (Fin N) where
 Adj u v:= G.Adj u v∧ s(u,v)∉ E
 symm:=⟨by
   intro u v h
   exact ⟨h.1.symm,by simpa only [Sym2.eq_swap] using h.2⟩⟩
 loopless:=⟨by intro v h;exact h.1.ne rfl⟩
namespace tI
variable {G M: SimpleGraph (Fin N)} {ell: ℕ} (S: tI G M ell)
def DH (E: Finset (Sym2 (Fin N)))
   (hMatched:∀u v,M.Adj u v→ s(u,v)∉ E)
   (hMemory:∀r R,S.ND.state r= some R→∀u v,(u,v)∈ R.tree.NS→ s(u,v)∉ E):
   tI G M ell where
 MG:= S.MG
 ND:= S.ND
 labels:= S.labels
 Nm:= S.Nm
 NV:= Ke S.NV E
 found:= S.found
 MF:= fun _ _ h=> S.MF h.1
 HK:= fun u v h=> S.HK u v h.1
 HQ:= fun u v hm hu=>⟨S.HQ u v hm hu,hMatched u v hm⟩
 EL:= S.EL
 DQ:= S.DQ
 Hu:= S.Hu
 DO:= S.DO
 I9:= fun r R hR u v he=>⟨S.I9 r R hR u v he,hMemory r R hR u v he⟩
 Iu:= S.Iu
 labelled:= S.labelled
 complete:= S.complete
 positive:= S.positive
 upper:= S.upper
end tI
end Be
end
noncomputable section
namespace Be
variable {I: Type}
lemma L6 (F: Finset I) (before after: I→ ℕ)
   (hmono:∀a∈ F,after a≤ before a) (hpos:∀a∈ F,1≤ after a):
   (∑a∈ F,(after a-1))+(F.filter (fun a=> after a< before a)).card≤∑a∈ F,(before a-1):= by
 have hc:(F.filter (fun a=> after a< before a)).card=∑a∈ F,if after a< before a then 1 else 0:= by
   rw [card_eq_sum_ones,sum_filter]
 rw [hc,←sum_add_distrib]
 apply sum_le_sum
 intro a ha
 have hm:= hmono a ha
 have hp:= hpos a ha
 split_ifs<;> omega
lemma zG (potential cost: ℕ→ ℕ) (hstep:∀t,potential (t+1)+cost t≤ potential t) (T: ℕ):
   potential T+∑t∈ range T,cost t≤ potential 0:= by
 induction T with
 | zero => simp
 | succ T ih =>
   rw [sum_range_succ]
   have hs:= hstep T
   omega
lemma KV (F: Finset I) (labels: I→ ℕ) (ell: ℕ) (hbound:∀a∈ F,labels a≤ ell+1):
   (∑a∈ F,(labels a-1))≤ ell*F.card:= by
 calc
   _≤∑_∈ F,ell:= sum_le_sum (fun a ha=> by have h:=hbound a ha;omega)
   _= _:= by simp [mul_comm]
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
namespace tI
def LN (S: tI G M ell): ℕ:=∑a: M.Dart,(S.labels a.toProd-1)
def Kw (S T: tI G M ell): Finset M.Dart:=
 univ.filter (fun a=> T.labels a.toProd< S.labels a.toProd)
lemma BU (S: tI G M ell): S.LN≤ 2*ell*matchingSize M:= by
 have h:= KV (univ: Finset M.Dart) (fun a=> S.labels a.toProd) ell (fun a _=> S.upper a.toProd)
 rw [card_univ,M.dart_card_eq_twice_card_edges] at h
 exact h.trans_eq (by unfold matchingSize;ring)
lemma D5 (S T: tI G M ell) (hmono:∀a,T.labels a≤ S.labels a):
   T.LN+(S.Kw T).card≤ S.LN:=
 L6 univ (fun a: M.Dart=> S.labels a.toProd) (fun a=> T.labels a.toProd)
   (fun a _=> hmono a.toProd) (fun a _=> T.positive a.toProd)
end tI
lemma Bb.Ae {S: tI G M ell} {x y: Fin N}
   {R: y7 S x y} (A: Bb R): A.Nj.LN+1≤ S.LN:= by
 have h:= S.D5 A.Nj A.Jj
 have hnon:(S.Kw A.Nj).Nonempty:= by
   exact ⟨⟨(y,R.NW),R.matched⟩,mem_filter.mpr ⟨mem_univ _,A.GS⟩⟩
 have hc: 1≤(S.Kw A.Nj).card:= hnon.card_pos
 omega
inductive Bf: tI G M ell→ tI G M ell→ Prop where
 | edge {S T} (mode: Bool) (x y: Fin N) (step: M3 mode x y S T): Bf S T
 | begin (S: tI G M ell) (limit: ℕ): Bf S (S.IX limit)
 | hold (S: tI G M ell) (limit: ℕ): Bf S (S.rC limit)
 | backtrack (S: tI G M ell): Bf S S.Dk
 | includeEdges (S: tI G M ell): Bf S S.z9
 | erase (S: tI G M ell) (E: Finset (Sym2 (Fin N)))
     (hM:∀u v,M.Adj u v→ s(u,v)∉ E)
     (hMemory:∀r R,S.ND.state r= some R→∀u v,(u,v)∈ R.tree.NS→ s(u,v)∉ E):
     Bf S (S.DH E hM hMemory)
 | idle (S: tI G M ell): Bf S S
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma M3.In {mode: Bool} {x y: Fin N} (h: M3 mode x y S T): S.Nm ⊆T.Nm:= by
 cases h with
 | augmentation A hflag => exact subset_union_left
 | extension hmode R hNo A => cases A<;> exact subset_refl _
 | skip hNo hNoExt => exact subset_refl _
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
namespace G8
def IP (F: G8 G M) (e: Fin N ×Fin N): Prop:=
 F.Mn (fun _ B=> B.tree.Reaches e∧ B.tree.Reaches e.swap)
lemma lO (F: G8 G M) (e: Fin N ×Fin N)
   (h:∃r,F.Reaches r e) (hr:∃r,F.Reaches r e.swap): F.IP e:= by
 obtain ⟨r,ha⟩:= h
 obtain ⟨s,hb⟩:= hr
 have heq:= F.pP r s e ha hb
 subst s
 obtain ⟨A,hA,ha⟩:= ha
 obtain ⟨B,hB,hb⟩:= hb
 have hAB: A= B:= Option.some.inj (hA.symm.trans hB)
 subst B
 exact ⟨r,A,hA,ha,hb⟩
end G8
lemma M3.lP {mode: Bool} {x y: Fin N} (h: M3 mode x y S T)
   (e: Fin N ×Fin N) (halive: e.1∉ T.Nm) (hs: S.ND.IP e): T.ND.IP e:= by
 cases h with
 | augmentation A hflag =>
   obtain ⟨r,R,hR,he,hr⟩:= hs
   have hmem: e.1∈ R.tree.vertices:=(R.tree.yG e he).1
   by_cases hra: r= A.ME
   · subst r
     have hRA: R= A.left:= Option.some.inj (hR.symm.trans A.HJ)
     subst R
     exact (halive (mem_union_right _ (mem_union_left _ hmem))).elim
   · by_cases hrb: r= A.L7
     · subst r
       have hRB: R= A.right:= Option.some.inj (hR.symm.trans A.GE)
       subst R
       exact (halive (mem_union_right _ (mem_union_right _ hmem))).elim
     · refine ⟨r,R,?_,he,hr⟩
       change (if r∈({A.ME,A.L7}:Finset (Fin N)) then none else S.ND.state r)= some R
       simp only [mem_insert,mem_singleton,hra,hrb,or_self,if_false]
       exact hR
 | extension hmode R hNo A => exact A.lQ e hs
 | skip hNo hNoExt => exact hs
lemma Bf.lP (h: Bf S T)
   (e: Fin N ×Fin N) (halive: e.1∉ T.Nm) (hs: S.ND.IP e): T.ND.IP e:= by
 cases h with
 | edge mode x y step => exact step.lP e halive hs
 | begin limit =>
   exact S.ND.Hw _ (fun _ R=> R.IX limit) (fun _ _=> rfl) (fun _ _ h=> h) hs
 | hold limit =>
   exact S.ND.Hw _ (fun _ R=> R.rC limit) (fun _ _=> rfl) (fun _ _ h=> h) hs
 | backtrack =>
   apply S.ND.Hw _ (fun _ R=> R.zS) _ _ hs
   · intro r R;unfold Lp.zS;split_ifs<;> rfl
   · intro r R hp;unfold Lp.zS;split_ifs<;> exact hp
 | includeEdges =>
   apply S.ND.Hw _ (fun _ R=> R.z8 S.NV S.MF)
     (fun _ R=> R.fA S.NV S.MF) _ hs
   intro r R hp
   exact ⟨R.tree.fJ _ _ e hp.1,R.tree.fJ _ _ e.swap hp.2⟩
 | erase E hM hMemory => exact hs
 | idle => exact hs
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell} {x y: Fin N}
lemma M2.split {mode: Bool} {es: List (Fin N ×Fin N)}
   (h: M2 mode es S T) (e: Fin N ×Fin N) (he: e∈ es):
   ∃(pre post: List (Fin N ×Fin N)) (U V: tI G M ell),
     es= pre++ e::post∧ M2 mode pre S U∧ M3 mode e.1 e.2 U V∧ M2 mode post V T:= by
 induction h with
 | nil S => simp at he
 | @cons x y es S U T step rest ih =>
   rcases List.mem_cons.mp he with he|he
   · subst e
     exact ⟨[],es,S,U,rfl,M2.nil S,step,rest⟩
   · obtain ⟨pre,post,V,W,hes,hpre,hstep,hpost⟩:= ih he
     exact ⟨(x,y)::pre,post,V,W,by simp only [List.cons_append,hes],M2.cons step hpre,hstep,hpost⟩
end Be
end
noncomputable section
namespace Be.G8
variable {N: ℕ} {G M: SimpleGraph (Fin N)} (F: G8 G M)
def n8 (H: SimpleGraph (Fin N)): Prop:=
 ∀r s,r≠ s→∀A B,F.state r= some A→ F.state s= some B→
   ∀u v,H.Adj u v→ u∈ A.tree.vertices→ v∈ B.tree.vertices→¬M.Adj u v→¬Nonempty (C3 (Mv G ((A.tree.NS ∪B.tree.NS) ∪{(u,v)})) M)
lemma nO (H: SimpleGraph (Fin N)) (hHG: H≤ G) (hNo: F.n8 H)
   (r s: Fin N) (a b: Fin N ×Fin N) (ha: F.Reaches r a) (hb: F.Reaches s b)
   (hedge: H.Adj a.2 b.2) (hM:¬M.Adj a.2 b.2): r= s:= by
 by_contra hne
 obtain ⟨A,hA,ha⟩:= ha
 obtain ⟨B,hB,hb⟩:= hb
 exact hNo r s hne A B hA hB a.2 b.2 hedge
   (A.tree.yG a ha).2 (B.tree.yG b hb).2 hM
   (A.tree.cP B.tree (F.disjoint r s hne A B hA hB) a b ha hb (hHG hedge) hM)
end Be.G8
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell} {x y: Fin N}
lemma M3.tS (h: M3 false x y S T) {r: Fin N} (R: Lp G M r)
   (hR: T.ND.state r= some R): S.ND.state r= some R:= by
 cases h with
 | augmentation A hflag =>
   change (if r∈({A.ME,A.L7}:Finset (Fin N)) then none else S.ND.state r)= some R at hR
   split_ifs at hR
   exact hR
 | extension hmode R hNo A => cases hmode
 | skip hNo hNoExt => exact hR
lemma M3.MF {mode: Bool} (h: M3 mode x y S T): T.NV≤ S.NV:= by
 cases h with
 | augmentation R hflag => exact fun _ _ h=> h.1
 | extension hmode R hNo A => cases A<;> exact le_rfl
 | skip hNo hNoExt => exact le_rfl
lemma M2.tS {es: List (Fin N ×Fin N)} (h: M2 false es S T)
   {r: Fin N} (R: Lp G M r) (hR: T.ND.state r= some R): S.ND.state r= some R:= by
 induction h with
 | nil S => exact hR
 | cons step rest ih => exact step.tS R (ih hR)
lemma M2.MF {mode: Bool} {es: List (Fin N ×Fin N)} (h: M2 mode es S T): T.NV≤ S.NV:= by
 induction h with
 | nil S => exact le_rfl
 | cons step rest ih => exact ih.trans step.MF
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
namespace G8
def JV (F: G8 G M) (a b: Fin N ×Fin N): Prop:=
 F.Mn (fun _ R=> R.tree.Mo a b)
end G8
lemma M3.q9 {mode: Bool} {x y: Fin N} (h: M3 mode x y S T)
   (a b: Fin N ×Fin N) (hM:¬M.Adj a.2 b.2) (halive: a.1∉ T.Nm)
   (hs: S.ND.JV a b): T.ND.JV a b:= by
 cases h with
 | augmentation A hflag =>
   obtain ⟨r,R,hR,he,hr,hcache⟩:= hs
   have hmem: a.1∈ R.tree.vertices:=(R.tree.yG a he).1
   by_cases hra: r= A.ME
   · subst r
     have hRA: R= A.left:= Option.some.inj (hR.symm.trans A.HJ)
     subst R
     exact (halive (mem_union_right _ (mem_union_left _ hmem))).elim
   · by_cases hrb: r= A.L7
     · subst r
       have hRB: R= A.right:= Option.some.inj (hR.symm.trans A.GE)
       subst R
       exact (halive (mem_union_right _ (mem_union_right _ hmem))).elim
     · refine ⟨r,R,?_,he,hr,hcache⟩
       change (if r∈({A.ME,A.L7}:Finset (Fin N)) then none else S.ND.state r)= some R
       simp only [mem_insert,mem_singleton,hra,hrb,or_self,if_false]
       exact hR
 | extension hmode R hNo A => exact A.q9 a b hM hs
 | skip hNo hNoExt => exact hs
lemma Bf.q9 (h: Bf S T)
   (a b: Fin N ×Fin N) (hM:¬M.Adj a.2 b.2) (halive: a.1∉ T.Nm)
   (hs: S.ND.JV a b): T.ND.JV a b:= by
 cases h with
 | edge mode x y step => exact step.q9 a b hM halive hs
 | begin limit =>
   exact S.ND.Hw _ (fun _ R=> R.IX limit) (fun _ _=> rfl) (fun _ _ h=> h) hs
 | hold limit =>
   exact S.ND.Hw _ (fun _ R=> R.rC limit) (fun _ _=> rfl) (fun _ _ h=> h) hs
 | backtrack =>
   apply S.ND.Hw _ (fun _ R=> R.zS) _ _ hs
   · intro r R;unfold Lp.zS;split_ifs<;> rfl
   · intro r R hp;unfold Lp.zS;split_ifs<;> exact hp
 | includeEdges =>
   apply S.ND.Hw _ (fun _ R=> R.z8 S.NV S.MF)
     (fun _ R=> R.fA S.NV S.MF) _ hs
   intro r R hp
   exact R.tree.dZ _ _ a b hp
 | erase E hMatched hMemory => exact hs
 | idle => exact hs
end Be
end
noncomputable section
namespace Be.G8
variable {N: ℕ} {G M: SimpleGraph (Fin N)} (F: G8 G M)
lemma gF (a: ℕ→ Fin N ×Fin N) (n: ℕ)
   (hlinks:∀i,i+1< n→ F.JV (a i) (a (i+1)).swap)
   (r: Fin N) (hfirst: F.Mm r (a 0).1) (i: ℕ) (hi: i< n): F.Mm r (a i).1:= by
 induction i with
 | zero => exact hfirst
 | succ i ih =>
   have hprev:= ih (by omega)
   obtain ⟨s,R,hR,ha,hb,hcache⟩:= hlinks i hi
   have has: F.Mm s (a i).1:=⟨R,hR,(R.tree.yG (a i) ha).1⟩
   have hrs:= F.BE r s (a i).1 hprev has
   subst s
   exact ⟨R,hR,(R.tree.yG (a (i+1)).swap hb).2⟩
lemma gG (hM: Matching G M) (a: ℕ→ Fin N ×Fin N) (n: ℕ)
   (hlinks:∀i,i+1< n→ F.JV (a i) (a (i+1)).swap)
   (hfirst:∃r,F.Mm r (a 0).1) (hmatched:∀i,i< n→ M.Adj (a i).1 (a i).2)
   (j: ℕ) (hj: j< n) (E: Finset (Fin N ×Fin N))
   (hE:∀e∈ E,∃i,i< n∧(e= a i∨ e=(a i).swap)):
   ∀r R,F.state r= some R→(a j).1∈ R.tree.vertices→∀e∈ E,e.1∈ R.tree.vertices:= by
 obtain ⟨s,hs⟩:= hfirst
 have hsj:= F.gF a n hlinks s hs j hj
 intro r R hR hjR e he
 have hsr:= F.BE s r (a j).1 hsj ⟨R,hR,hjR⟩
 subst s
 obtain ⟨i,hi,heq⟩:= hE e he
 have htail:= F.gF a n hlinks r hs i hi
 have hboth: F.Mm r e.1:= by
   rcases heq with heq|heq
   · rw [heq];exact htail
   · rw [heq]
     exact F.kC hM r (a i).1 (a i).2 htail (hmatched i hi)
 obtain ⟨B,hB,heB⟩:= hboth
 have hBR: B= R:= Option.some.inj (hB.symm.trans hR)
 subst B
 exact heB
end Be.G8
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
namespace Lp
variable {r: Fin N}
def height (R: Lp G M r): ℕ:= R.active.elim 0 v9.length
def Fw (R: Lp G M r): ℕ:=
 if R.NU|| R.modified then 0 else R.active.elim 0 (fun P=> if 0< P.length then 1 else 0)
lemma Hx (R: Lp G M r) (ell: ℕ) (lab: Fin N ×Fin N→ ℕ) (h: R.Mq ell lab):
   R.height≤ ell:= by
 cases hp: R.active with
 | none => simp [height,hp]
 | some P => simpa only [height,hp,Option.elim_some] using (h P hp).1
lemma zT (R: Lp G M r): R.zS.height+R.Fw= R.height:= by
 unfold zS Fw
 split_ifs with h
 · simp
 · cases hp: R.active with
   | none => simp [backtrack,height,hp]
   | some P =>
     by_cases hpos: 0< P.length
     · simp only [backtrack,height,hp,Option.bind_some,dif_pos hpos,Option.elim_some,if_pos hpos]
       change P.length-1+1=P.length
       omega
     · have hlen: P.length= 0:= by omega
       simp [backtrack,height,hp,hpos,hlen]
end Lp
namespace G8
def height (F: G8 G M): ℕ:=∑r: Fin N,(F.state r).elim 0 Lp.height
def Fw (F: G8 G M): ℕ:=∑r: Fin N,(F.state r).elim 0 Lp.Fw
lemma rA (F H: G8 G M) {alpha: Fin N} (A: Lp G M alpha)
   (heq: H.state= Function.update F.state alpha (some A)) (ell: ℕ) (hA: A.height≤ ell):
   H.height≤ F.height+ell:= by
 calc
   H.height≤∑r: Fin N,((F.state r).elim 0 Lp.height+ if r=alpha then ell else 0):= by
     apply sum_le_sum
     intro r hr
     rw [heq]
     by_cases hra: r= alpha
     · subst r
       rw [Function.update_self]
       simp only [Option.elim_some,ite_true]
       omega
     · rw [Function.update_of_ne hra]
       simp [hra]
   _= F.height+ell:= by simp [height,sum_add_distrib]
lemma rB (F H: G8 G M) {alpha beta: Fin N} (hab: alpha≠ beta)
   (A: Lp G M alpha) (B: Lp G M beta)
   (heq: H.state= F.E2 A B) (ell: ℕ) (hA: A.height≤ ell) (hB: B.height≤ ell):
   H.height≤ F.height+2*ell:= by
 calc
   H.height≤∑r: Fin N,((F.state r).elim 0 Lp.height+(if r=alpha then ell else 0)+(if r=beta then ell else 0)):= by
     apply sum_le_sum
     intro r hr
     rw [heq]
     by_cases hra: r= alpha
     · subst r
       rw [F.CZ hab]
       simp only [Option.elim_some,ite_true,if_neg hab,add_zero]
       omega
     · by_cases hrb: r= beta
       · subst r
         rw [F.E3]
         simp only [Option.elim_some,if_neg hab.symm,ite_true,add_zero]
         omega
       · rw [F.C0 A B r hra hrb]
         simp [hra,hrb]
   _= F.height+2*ell:= by simp [height,sum_add_distrib];omega
lemma e6 (F H: G8 G M) {alpha: Fin N} (A: Lp G M alpha)
   (heq: H.state= Function.update F.state alpha (some A)) (ell: ℕ) (lab: Fin N ×Fin N→ ℕ)
   (hH: H.Mq ell lab): H.height≤ F.height+ell:= by
 apply rA F H A heq ell
 exact A.Hx ell lab (hH alpha A (by rw [heq];exact Function.update_self _ _ _))
lemma e7 (F H: G8 G M) {alpha beta: Fin N} (hab: alpha≠ beta)
   (A: Lp G M alpha) (B: Lp G M beta)
   (heq: H.state= F.E2 A B) (ell: ℕ) (lab: Fin N ×Fin N→ ℕ)
   (hH: H.Mq ell lab): H.height≤ F.height+2*ell:= by
 apply rB F H hab A B heq ell
 · exact A.Hx ell lab (hH alpha A (by rw [heq];exact F.CZ hab A B))
 · exact B.Hx ell lab (hH beta B (by rw [heq];exact F.E3 A B))
lemma mU (F: G8 G M) (D: Finset (Fin N)):(F.Jy D).height≤ F.height:= by
 apply sum_le_sum
 intro r hr
 change (if r∈ D then none else F.state r).elim 0 Lp.height≤ _
 split_ifs
 · exact Nat.zero_le _
 · exact le_rfl
lemma FU (F: G8 G M) (f:∀r,Lp G M r→ Lp G M r)
   (hv:∀r R,(f r R).tree.vertices= R.tree.vertices) (hh:∀r R,(f r R).height= R.height):
   (F.LU f hv).height= F.height:= by
 apply sum_congr rfl
 intro r hr
 change ((F.state r).map (f r)).elim 0 Lp.height= _
 cases hp: F.state r with
 | none => rfl
 | some R => exact hh r R
end G8
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S: tI G M ell} {x y: Fin N}
lemma Bb.BP {R: y7 S x y} (A: Bb R):
   A.Nj.ND.height≤ S.ND.height+2*ell:= by
 cases A with
 | single hOwner =>
   have h:= G8.e6 S.ND (Bb.single hOwner).Nj.ND
     _ rfl ell _ (Bb.single hOwner).Nj.labelled
   omega
 | inactive D B hB hAT hBT hStem hTarget hInactive =>
   exact G8.e7 S.ND _ D.distinct _ _ rfl ell _
     (Bb.inactive D B hB hAT hBT hStem hTarget hInactive).Nj.labelled
 | active D B hB hAT hBT hStem hTarget hActive =>
   exact G8.e7 S.ND _ D.data.distinct _ _ rfl ell _
     (Bb.active D B hB hAT hBT hStem hTarget hActive).Nj.labelled
namespace tI
variable (S: tI G M ell)
lemma uA (limit: ℕ):(S.IX limit).ND.height= S.ND.height:=
 S.ND.FU (fun _ R=> R.IX limit) (fun _ _=> rfl) (fun _ _=> rfl)
lemma d0 (limit: ℕ):(S.rC limit).ND.height= S.ND.height:=
 S.ND.FU (fun _ R=> R.rC limit) (fun _ _=> rfl) (fun _ _=> rfl)
lemma iX: S.z9.ND.height= S.ND.height:=
 S.ND.FU _ (fun _ R=> R.fA S.NV S.MF) (fun _ _=> rfl)
lemma zT: S.Dk.ND.height+S.ND.Fw= S.ND.height:= by
 rw [G8.height,G8.Fw,←sum_add_distrib]
 apply sum_congr rfl
 intro r hr
 change ((S.ND.state r).map (fun R=> R.zS)).elim 0 Lp.height+
   (S.ND.state r).elim 0 Lp.Fw= _
 cases hp: S.ND.state r with
 | none => rfl
 | some R => exact R.zT
end tI
end Be
end
noncomputable section
namespace Be.G8
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
def GH (F: G8 G M) (p:∀r,Lp G M r→ Prop): Finset (Fin N):=
 univ.filter (fun r=>∃R,F.state r= some R∧ p r R)
lemma xO (F: G8 G M) (p:∀r,Lp G M r→ Prop) (r: Fin N):
   r∈ F.GH p↔∃R,F.state r= some R∧ p r R:= by simp [GH]
def IS (F: G8 G M): Finset (Fin N):= F.GH (fun _ R=> R.active.isSome)
def Gc (F: G8 G M): Finset (Fin N):= F.GH (fun _ R=> R.modified)
lemma fN (F H: G8 G M) (p:∀r,Lp G M r→ Prop)
   {alpha: Fin N} (A: Lp G M alpha) (heq: H.state= Function.update F.state alpha (some A)):
   H.GH p ⊆F.GH p ∪{alpha}:= by
 intro r hr
 obtain ⟨R,hR,hp⟩:=(H.xO p r).mp hr
 by_cases hra: r= alpha
 · exact mem_union_right _ (mem_singleton.mpr hra)
 · rw [heq,Function.update_of_ne hra] at hR
   exact mem_union_left _ ((F.xO p r).mpr ⟨R,hR,hp⟩)
lemma fO (F H: G8 G M) (p:∀r,Lp G M r→ Prop)
   {alpha beta: Fin N} (A: Lp G M alpha) (B: Lp G M beta)
   (heq: H.state= F.E2 A B):
   H.GH p ⊆F.GH p ∪{alpha,beta}:= by
 intro r hr
 obtain ⟨R,hR,hp⟩:=(H.xO p r).mp hr
 by_cases hra: r= alpha
 · exact mem_union_right _ (mem_insert.mpr (Or.inl hra))
 · by_cases hrb: r= beta
   · exact mem_union_right _ (mem_insert.mpr (Or.inr (mem_singleton.mpr hrb)))
   · rw [heq,F.C0 A B r hra hrb] at hR
     exact mem_union_left _ ((F.xO p r).mpr ⟨R,hR,hp⟩)
lemma jM (F H: G8 G M) (p:∀r,Lp G M r→ Prop)
   {alpha: Fin N} (A: Lp G M alpha) (heq: H.state= Function.update F.state alpha (some A))
   (hA: p alpha A→∃Q,F.state alpha= some Q∧ p alpha Q):
   H.GH p ⊆F.GH p:= by
 intro r hr
 obtain ⟨R,hR,hp⟩:=(H.xO p r).mp hr
 rw [heq] at hR
 by_cases hra: r= alpha
 · subst r
   rw [Function.update_self] at hR
   cases Option.some.inj hR
   exact (F.xO p alpha).mpr (hA hp)
 · rw [Function.update_of_ne hra] at hR
   exact (F.xO p r).mpr ⟨R,hR,hp⟩
lemma jO (F H: G8 G M) (p:∀r,Lp G M r→ Prop)
   {alpha beta: Fin N} (hab: alpha≠ beta)
   (A: Lp G M alpha) (B: Lp G M beta) (heq: H.state= F.E2 A B)
   (hA: p alpha A→∃Q,F.state alpha= some Q∧ p alpha Q)
   (hB: p beta B→∃Q,F.state beta= some Q∧ p beta Q):
   H.GH p ⊆F.GH p:= by
 intro r hr
 obtain ⟨R,hR,hp⟩:=(H.xO p r).mp hr
 rw [heq] at hR
 by_cases hra: r= alpha
 · subst r
   rw [F.CZ hab] at hR
   cases Option.some.inj hR
   exact (F.xO p alpha).mpr (hA hp)
 · by_cases hrb: r= beta
   · subst r
     rw [F.E3] at hR
     cases Option.some.inj hR
     exact (F.xO p beta).mpr (hB hp)
   · rw [F.C0 A B r hra hrb] at hR
     exact (F.xO p r).mpr ⟨R,hR,hp⟩
lemma jN (F H: G8 G M) (p:∀r,Lp G M r→ Prop)
   {alpha: Fin N} (A: Lp G M alpha) (heq: H.state= Function.update F.state alpha (some A)):
   (H.GH p).card≤(F.GH p).card+1:= by
 exact (card_le_card (fN F H p A heq)).trans ((card_union_le _ _).trans_eq (by rw [card_singleton]))
lemma jP (F H: G8 G M) (p:∀r,Lp G M r→ Prop)
   {alpha beta: Fin N} (A: Lp G M alpha) (B: Lp G M beta)
   (heq: H.state= F.E2 A B):
   (H.GH p).card≤(F.GH p).card+2:= by
 have hs:= card_le_card (fO F H p A B heq)
 have hu:= card_union_le (F.GH p) ({alpha,beta}:Finset (Fin N))
 have hp:({alpha,beta}:Finset (Fin N)).card≤ 2:=(card_insert_le _ _).trans (by rw [card_singleton])
 omega
lemma dE (F: G8 G M) (p:∀r,Lp G M r→ Prop) (D: Finset (Fin N)):
   (F.Jy D).GH p ⊆F.GH p:= by
 intro r hr
 obtain ⟨R,hR,hp⟩:=((F.Jy D).xO p r).mp hr
 change (if r∈ D then none else F.state r)= some R at hR
 split_ifs at hR
 exact (F.xO p r).mpr ⟨R,hR,hp⟩
lemma sW (F: G8 G M) (p:∀r,Lp G M r→ Prop)
   (f:∀r,Lp G M r→ Lp G M r)
   (hv:∀r R,(f r R).tree.vertices= R.tree.vertices)
   (hp:∀r R,p r (f r R)→ p r R):
   (F.LU f hv).GH p ⊆F.GH p:= by
 intro r hr
 obtain ⟨R,hR,hpR⟩:=((F.LU f hv).xO p r).mp hr
 change (F.state r).map (f r)= some R at hR
 obtain ⟨Q,hQ,hQR⟩:= Option.map_eq_some_iff.mp hR
 exact (F.xO p r).mpr ⟨Q,hQ,hp r Q (hQR ▸hpR)⟩
end Be.G8
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell} {x y: Fin N}
lemma Bb.xU {R: y7 S x y} (A: Bb R):
   A.Nj.ND.Gc.card≤ S.ND.Gc.card+2:= by
 cases A with
 | single hOwner =>
   have h:= G8.jN S.ND (Bb.single hOwner).Nj.ND
     (fun _ R=> R.modified) _ rfl
   change (Bb.single hOwner).Nj.ND.Gc.card≤ S.ND.Gc.card+1 at h
   omega
 | inactive D B hB hAT hBT hStem hTarget hInactive =>
   exact G8.jP S.ND _ (fun _ R=> R.modified) _ _ rfl
 | active D B hB hAT hBT hStem hTarget hActive =>
   exact G8.jP S.ND _ (fun _ R=> R.modified) _ _ rfl
lemma M3.rZ {mode: Bool} (h: M3 mode x y S T):
   T.ND.Gc.card+2*T.LN≤ S.ND.Gc.card+2*S.LN:= by
 cases h with
 | augmentation R hflag =>
   have hcard:= card_le_card (S.ND.dE (fun _ R=> R.modified) {R.ME,R.L7})
   change (S.ND.Jy _).Gc.card+2*S.LN≤ _
   exact Nat.add_le_add_right hcard _
 | extension hmode R hNo A =>
   have hcard:= A.xU
   have hdrop:= A.Ae
   omega
 | skip hNo hNoExt => exact le_rfl
lemma M2.rZ {mode: Bool} {es: List (Fin N ×Fin N)} (h: M2 mode es S T):
   T.ND.Gc.card+2*T.LN≤ S.ND.Gc.card+2*S.LN:= by
 induction h with
 | nil S => exact le_rfl
 | cons step rest ih => exact ih.trans step.rZ
lemma tI.dQ (S: tI G M ell) (limit: ℕ):
   (S.IX limit).ND.Gc=∅:= by
 apply eq_empty_iff_forall_notMem.mpr
 intro r hr
 obtain ⟨R,hR,hm⟩:=((S.IX limit).ND.xO (fun _ R=> R.modified) r).mp hr
 change (S.ND.state r).map (fun R=> R.IX limit)= some R at hR
 obtain ⟨Q,hQ,hQR⟩:= Option.map_eq_some_iff.mp hR
 rw [←hQR] at hm
 change false= true at hm
 cases hm
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell} {x y: Fin N}
namespace tI
def G1 (S: tI G M ell): ℕ:= S.ND.height+2*ell*S.LN
lemma rank_mono (S T: tI G M ell) (h:∀a,T.labels a≤ S.labels a): T.LN≤ S.LN:= by
 exact (Nat.le_add_right _ _).trans (S.D5 T h)
lemma A9 (S: tI G M ell) (limit: ℕ):(S.IX limit).G1= S.G1:= by
 change (S.IX limit).ND.height+2*ell*S.LN= _
 rw [S.uA]
 rfl
lemma iC (S: tI G M ell) (limit: ℕ):
   (S.rC limit).G1= S.G1:= by
 change (S.rC limit).ND.height+2*ell*S.LN= _
 rw [S.d0]
 rfl
lemma n7 (S: tI G M ell): S.z9.G1= S.G1:= by
 change S.z9.ND.height+2*ell*S.LN= _
 rw [S.iX]
 rfl
lemma E7 (S: tI G M ell):
   S.Dk.G1+S.ND.Fw= S.G1:= by
 change S.Dk.ND.height+2*ell*S.LN+S.ND.Fw= _
 have h:= S.zT
 unfold G1
 omega
end tI
lemma Bb.Ml {R: y7 S x y} (A: Bb R): A.Nj.G1≤ S.G1:= by
 have hh:= A.BP
 have hr:= Nat.mul_le_mul_left (2*ell) A.Ae
 rw [Nat.mul_add,Nat.mul_one] at hr
 unfold tI.G1
 omega
lemma M3.Ml {mode: Bool} (h: M3 mode x y S T): T.G1≤ S.G1:= by
 cases h with
 | augmentation R hflag =>
   exact Nat.add_le_add_right (S.ND.mU {R.ME,R.L7}) _
 | extension hmode R hNo A => exact A.Ml
 | skip hNo hNoExt => exact le_rfl
lemma M2.Ml {mode: Bool} {es: List (Fin N ×Fin N)} (h: M2 mode es S T): T.G1≤ S.G1:= by
 induction h with
 | nil S => exact le_rfl
 | cons step rest ih => exact ih.trans step.Ml
end Be
end
noncomputable section
namespace Be.G8
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
lemma nY (F: G8 G M) (D: Finset (Fin N)) (limit: ℕ)
   (hlarge:∀r∈ D,∃R,F.state r= some R∧ limit+1≤ R.tree.vertices.card):
   D.card*limit≤ 2*matchingSize M:= by
 let I:={r// r∈ D}
 let state (i: I): Lp G M i.val:= Classical.choose (hlarge i.val i.property)
 have hs (i: I): F.state i.val= some (state i)∧ limit+1≤(state i).tree.vertices.card:=
   Classical.choose_spec (hlarge i.val i.property)
 have hd: Set.Pairwise ((univ: Finset I): Set I) (fun i j=> Disjoint (state i).tree.vertices (state j).tree.vertices):= by
   intro i hi j hj hij
   exact F.disjoint i.val j.val (fun he=> hij (Subtype.ext he)) (state i) (state j) (hs i).1 (hs j).1
 have h:= i7 (univ: Finset I) (fun i=> i.val) (fun i=>(state i).tree) hd limit
   (fun i _=>(hs i).2)
 simpa [I] using h
def LI (F: G8 G M): Finset (Fin N):=
 univ.filter (fun r=>∃R,F.state r= some R∧ R.NU= true)
lemma Ga (F: G8 G M) (r: Fin N):
   r∈ F.LI↔∃R,F.state r= some R∧ R.NU= true:= by simp [LI]
lemma Mp.z6 {F H: G8 G M} (h: Mp F H): H.LI ⊆F.LI:= by
 intro r hr
 obtain ⟨R,hR,hh⟩:=(H.Ga r).mp hr
 obtain ⟨Q,hQ,hRQ⟩:= h r R hR
 exact (F.Ga r).mpr ⟨Q,hQ,hRQ.symm.trans hh⟩
end Be.G8
namespace Be.tI
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma iH (S: tI G M ell) (limit: ℕ):
   (S.IX (limit+1)).ND.LI.card*limit≤ 2*matchingSize M:= by
 apply (S.IX (limit+1)).ND.nY
 intro r hr
 obtain ⟨R,hR,hh⟩:=((S.IX (limit+1)).ND.Ga r).mp hr
 have hR':(S.ND.state r).map (fun R=> R.IX (limit+1))= some R:= hR
 obtain ⟨Q,hQ,hQR⟩:= Option.map_eq_some_iff.mp hR'
 refine ⟨R,hR,?_⟩
 rw [←hQR] at hh ⊢
 change (Q.NU&& decide (limit+1≤ Q.tree.vertices.card))= true at hh
 cases hheld: Q.NU<;> simp [hheld] at hh
 exact hh
lemma e2 (S T: tI G M ell) (limit: ℕ)
   (es: List (Fin N ×Fin N)) (h: M2 true es (S.IX (limit+1)) T):
   T.ND.LI.card*limit≤ 2*matchingSize M:= by
 exact (Nat.mul_le_mul_right limit (card_le_card h.LJ.z6)).trans (S.iH limit)
end Be.tI
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
namespace G8
def Ky (F: G8 G M) (limit: ℕ): Finset (Fin N):=
 F.GH (fun _ R=> limit+1≤ R.tree.vertices.card)
lemma xC (F: G8 G M) (limit: ℕ):
   (F.Ky limit).card*limit≤ 2*matchingSize M:= by
 apply F.nY
 intro r hr
 exact (F.xO _ r).mp hr
end G8
namespace tI
variable (S: tI G M ell)
lemma a7 (limit: ℕ):
   (S.rC (limit+1)).ND.LI ⊆S.ND.LI ∪S.ND.Ky limit:= by
 intro r hr
 obtain ⟨R,hR,hh⟩:=((S.rC (limit+1)).ND.Ga r).mp hr
 change (S.ND.state r).map (fun R=> R.rC (limit+1))= some R at hR
 obtain ⟨Q,hQ,hQR⟩:= Option.map_eq_some_iff.mp hR
 rw [←hQR] at hh
 cases hheld: Q.NU with
 | false =>
   have hlarge: limit+1≤ Q.tree.vertices.card:= by simpa [Lp.rC,hheld] using hh
   exact mem_union_right _ ((S.ND.xO _ r).mpr ⟨Q,hQ,hlarge⟩)
 | true => exact mem_union_left _ ((S.ND.Ga r).mpr ⟨Q,hQ,hheld⟩)
lemma eE (U: tI G M ell) (limit: ℕ)
   (es: List (Fin N ×Fin N)) (h: M2 true es (S.IX (limit+1)) U):
   (U.rC (limit+1)).ND.LI.card*limit≤ 4*matchingSize M:= by
 have hcard:=(card_le_card (U.a7 limit)).trans (card_union_le _ _)
 have hmul:= Nat.mul_le_mul_right limit hcard
 have hh:= S.e2 U limit es h
 have hl:= U.ND.xC limit
 nlinarith
lemma cD (limit: ℕ):
   (S.rC limit).ND.Gc= S.ND.Gc:= by
 ext r
 simp only [G8.Gc,G8.GH,mem_filter,mem_univ,true_and]
 change (∃R,(S.ND.state r).map (fun R=> R.rC limit)= some R∧ R.modified= true)↔ _
 cases hr: S.ND.state r<;> simp [hr,Lp.rC]
end tI
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell} {x y: Fin N}
lemma Bb.qP {R: y7 S x y} (A: Bb R):
   A.Nj.ND.IS ⊆S.ND.IS:= by
 cases A with
 | single hOwner =>
   apply G8.jM S.ND _ (fun _ R=> R.active.isSome) _ rfl
   intro h
   exact ⟨R.state,R.present,by simp [R.Lq]⟩
 | inactive D B hB hAT hBT hStem hTarget hInactive =>
   apply G8.jO S.ND _ (fun _ R=> R.active.isSome) D.distinct _ _ rfl
   · intro h
     exact ⟨R.state,R.present,by simp [R.Lq]⟩
   · intro h
     exact ⟨B,hB,h⟩
 | active D B hB hAT hBT hStem hTarget hActive =>
   apply G8.jO S.ND _ (fun _ R=> R.active.isSome) D.data.distinct _ _ rfl
   · intro h
     exact ⟨R.state,R.present,by simp [R.Lq]⟩
   · intro h
     exact ⟨B,hB,by simp [hActive]⟩
lemma M3.qP {mode: Bool} (h: M3 mode x y S T): T.ND.IS ⊆S.ND.IS:= by
 cases h with
 | augmentation R hflag => exact S.ND.dE (fun _ R=> R.active.isSome) _
 | extension hmode R hNo A => exact A.qP
 | skip hNo hNoExt => exact subset_refl _
lemma M2.qP {mode: Bool} {es: List (Fin N ×Fin N)} (h: M2 mode es S T):
   T.ND.IS ⊆S.ND.IS:= by
 induction h with
 | nil S => exact subset_refl _
 | cons step rest ih => exact ih.trans step.qP
lemma Lp.mD {r: Fin N} (R: Lp G M r):
   R.zS.active.isSome→ R.active.isSome:= by
 unfold zS
 split_ifs with h
 · exact id
 · cases hp: R.active with
   | none => simp [backtrack,hp]
   | some P => simp [hp]
lemma Bf.qP (h: Bf S T): T.ND.IS ⊆S.ND.IS:= by
 cases h with
 | edge mode x y step => exact step.qP
 | begin limit => exact S.ND.sW (fun _ R=> R.active.isSome) (fun _ R=> R.IX limit) (fun _ _=> rfl) (fun _ _ h=> h)
 | hold limit => exact S.ND.sW (fun _ R=> R.active.isSome) (fun _ R=> R.rC limit) (fun _ _=> rfl) (fun _ _ h=> h)
 | backtrack => exact S.ND.sW (fun _ R=> R.active.isSome) (fun _ R=> R.zS) (by intro r R;unfold Lp.zS;split_ifs<;> rfl) (fun _ R h=> R.mD h)
 | includeEdges => exact S.ND.sW (fun _ R=> R.active.isSome) (fun _ R=> R.z8 S.NV S.MF) (fun _ R=> R.fA S.NV S.MF) (fun _ _ h=> h)
 | erase E hM hMemory => exact subset_refl _
 | idle => exact subset_refl _
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma Lp.iG {r: Fin N} (R: Lp G M r)
   (hactive: R.zS.active.isSome):
   R.NU= true∨ R.modified= true∨ 0< R.Fw:= by
 by_cases h:(R.NU|| R.modified)= true
 · cases hh: R.NU<;> cases hm: R.modified<;> simp_all
 · right;right
   cases hp: R.active with
   | none => simp [zS,h,backtrack,hp] at hactive
   | some P =>
     by_cases hpos: 0< P.length
     · simp [Fw,h,hp,hpos]
     · simp [zS,h,backtrack,hp,hpos] at hactive
namespace G8
def wL (F: G8 G M): Finset (Fin N):=
 univ.filter (fun r=> 0<(F.state r).elim 0 Lp.Fw)
lemma f5 (F: G8 G M): F.wL.card≤ F.Fw:= by
 rw [wL,card_eq_sum_ones,sum_filter]
 apply sum_le_sum
 intro r hr
 split_ifs<;> omega
end G8
namespace tI
variable (S: tI G M ell)
lemma bY:
   S.Dk.ND.IS ⊆(S.ND.LI ∪S.ND.Gc) ∪S.ND.wL:= by
 intro r hr
 obtain ⟨R,hR,hact⟩:=(S.Dk.ND.xO _ r).mp hr
 change (S.ND.state r).map (fun R=> R.zS)= some R at hR
 obtain ⟨Q,hQ,hQR⟩:= Option.map_eq_some_iff.mp hR
 have hactive: Q.zS.active.isSome:= by rwa [hQR]
 rcases Q.iG hactive with hh|hm|hb
 · exact mem_union_left _ (mem_union_left _ ((S.ND.Ga r).mpr ⟨Q,hQ,hh⟩))
 · exact mem_union_left _ (mem_union_right _ ((S.ND.xO _ r).mpr ⟨Q,hQ,hm⟩))
 · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,by simpa only [hQ,Option.elim_some] using hb⟩)
lemma jZ:
   S.Dk.ND.IS.card≤ S.ND.LI.card+S.ND.Gc.card+S.ND.Fw:= by
 have hs:= card_le_card S.bY
 have hu:= card_union_le (S.ND.LI ∪S.ND.Gc) S.ND.wL
 have hu':= card_union_le S.ND.LI S.ND.Gc
 have hb:= S.ND.f5
 omega
end tI
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
namespace tI
def zA (S: tI G M ell): Prop:=
 ∀r R,S.ND.state r= some R→∀u v,S.NV.Adj u v→
   u∈ R.tree.vertices→ v∈ R.tree.vertices→¬M.Adj u v→(u,v)∈ R.tree.NS
lemma aX (S: tI G M ell): S.z9.zA:= by
 intro r R hR u v huv hu hv hM
 change (S.ND.state r).map (fun R=> R.z8 S.NV S.MF)= some R at hR
 obtain ⟨Q,hQ,hQR⟩:= Option.map_eq_some_iff.mp hR
 rw [←hQR] at hu hv ⊢
 rw [Q.fA] at hu hv
 let C: Finset (Fin N ×Fin N):= univ.filter (fun e=> S.NV.Adj e.1 e.2)
 have hC:∀u v,(u,v)∈ C→ G.Adj u v:= fun u v h=> S.MF (mem_filter.mp h).2
 apply (Q.tree.FX C hC).Cl
 exact Q.tree.i0 C hC u v (mem_filter.mpr ⟨mem_univ _,huv⟩) hM hu hv
lemma mT (S: tI G M ell) (hInternal: S.zA)
   (hNo: S.ND.n8 S.NV)
   (a b: Fin N ×Fin N) (ha:∃r,S.ND.Reaches r a) (hb:∃r,S.ND.Reaches r b)
   (hlive: S.NV.Adj a.2 b.2) (hM:¬M.Adj a.2 b.2): S.ND.JV a b:= by
 obtain ⟨r,ha⟩:= ha
 obtain ⟨s,hb⟩:= hb
 have heq:= S.ND.nO S.NV S.MF hNo r s a b ha hb hlive hM
 subst s
 obtain ⟨A,hA,ha⟩:= ha
 obtain ⟨B,hB,hb⟩:= hb
 have hAB: A= B:= Option.some.inj (hA.symm.trans hB)
 subst B
 exact ⟨r,A,hA,ha,hb,hInternal r A hA a.2 b.2 hlive (A.tree.yG a ha).2 (A.tree.yG b hb).2 hM⟩
end tI
variable {S T: tI G M ell}
lemma M2.iL {es: List (Fin N ×Fin N)} (h: M2 false es S T)
   (hS: S.zA): T.zA:= by
 intro r R hR u v huv hu hv hM
 exact hS r R (h.tS R hR) u v (h.MF huv) hu hv hM
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
namespace Bi
variable {r: Fin N} (A: Bi G M r)
lemma kW (hM: Matching G M) (u v: Fin N) (hm: M.Adj u v) (hu: u∈ A.vertices):
   (Mv G A.NS).Adj u v:= by
 rcases A.wS u hu with hur|hcovered
 · rw [hur] at hm
   exact (A.L9 v hm).elim
 · obtain ⟨x,y,hxy,hMxy,hux|huy⟩:= hcovered
   · subst u
     have hv:= qJ.gP G M hM x v y hm hMxy
     subst v
     exact ⟨hM.1 hMxy,Or.inl hxy⟩
   · subst u
     have hv:= qJ.gP G M hM y v x hm hMxy.symm
     subst v
     exact ⟨hM.1 hMxy.symm,Or.inr hxy⟩
end Bi
namespace v9
variable {r: Fin N} (P: v9 G M r)
def Nq (H: SimpleGraph (Fin N)) (h:∀i,i< 2*P.length→ H.Adj (P.vertex i) (P.vertex (i+1))):
   v9 H M r where
 length:= P.length
 vertex:= P.vertex
 first:= P.first
 injective:= P.injective
 Mu:= h
 MG:= P.MG
 L9:= P.L9
end v9
variable {S T: tI G M ell}
end Be
end
noncomputable section
namespace Be.Bi
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {r: Fin N}
lemma An (S: Bi G M r) {u v: Fin N}
   (h:(Mv G S.NS).Adj u v): u∈S.vertices∧ v∈S.vertices:= by
 rcases h.2 with h|h
 · exact S.Ft u v h
 · exact (S.Ft v u h).symm
lemma B8 (S: Bi G M r) (a: Fin N ×Fin N):
   (a∈S.NS∨ a.swap∈S.NS)↔(Mv G S.NS).Adj a.1 a.2:= by
 constructor
 · intro h
   exact ⟨h.elim (S.valid _ _) (fun he=>(S.valid _ _ he).symm),h⟩
 · exact And.right
lemma jD (S T: Bi G M r)
   (hMemory: Mv G S.NS=Mv G T.NS): S.normalized=T.normalized:= by
 apply FJ
 ext a
 change a∈S.KK↔ a∈T.KK
 simp only [KK,mem_filter,mem_univ,true_and]
 have hEdge:(a∈S.NS∨ a.swap∈S.NS)↔(a∈T.NS∨ a.swap∈T.NS):= by
   rw [S.B8,T.B8,hMemory]
 have hReach: S.Reaches a↔ T.Reaches a:= by
   unfold Reaches
   rw [hMemory]
 rw [hEdge,hReach]
lemma wN (S: Bi G M r) (hM: Matching G M)
   (C: Finset (Fin N ×Fin N)) (hC:∀u v,(u,v)∈C→ G.Adj u v) (hSub: S.NS⊆C)
   (u v: Fin N):
   (Mv G (S.FX C hC).NS).Adj u v↔
     (Mv G C).Adj u v∧ u∈S.vertices∧ v∈S.vertices:= by
 constructor
 · intro h
   have hEdge:=Fs _ _ (S.o0 C hC hSub) h
   have hEnds:=(S.FX C hC).An h
   rw [S.kK] at hEnds
   exact ⟨hEdge,hEnds⟩
 · rintro ⟨hEdge,hu,hv⟩
   by_cases hMatch: M.Adj u v
   · exact (S.FX C hC).kW hM u v hMatch (by rw [S.kK];exact hu)
   · rcases hEdge.2 with hArc|hArc
     · exact ⟨hEdge.1,Or.inl (S.i0 C hC u v hArc hMatch hu hv)⟩
     · exact ⟨hEdge.1,Or.inr (S.i0 C hC v u hArc (fun h=>hMatch h.symm) hv hu)⟩
lemma oN (S T: Bi G M r) (hM: Matching G M)
   (C: Finset (Fin N ×Fin N)) (hC:∀u v,(u,v)∈C→ G.Adj u v)
   (hS: S.NS⊆C) (hT: T.NS⊆C) (hVertices: S.vertices=T.vertices):
   (S.FX C hC).normalized=(T.FX C hC).normalized:= by
 apply jD
 ext u v
 rw [S.wN hM C hC hS,T.wN hM C hC hT,hVertices]
end Be.Bi
end
noncomputable section
namespace Be
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)}
namespace wF
variable (E: wF G M H K)
lemma Eb {A B: Finset (Fin N ×Fin N)} (h: A⊆B): E.Nc A⊆E.Nc B:= image_subset_image h
end wF
namespace v9
variable (E: wF G M H K) {r: Fin N}
lemma HC (Q: v9 H K (E.toFun r)) (A: Finset (Fin N ×Fin N))
   (hQ: Q.Nv (E.Nc A)) (i: ℕ) (hi: i≤ 2*Q.length):
   Q.vertex i∈Set.range E.toFun:= by
 by_cases hZero: i=0
 · rw [hZero,Q.first]; exact ⟨r,rfl⟩
 · have he:=hQ (i-1) (by omega)
   obtain ⟨⟨a,b⟩,ha,hEq⟩:=mem_image.mp he
   have hEnd:=congrArg Prod.snd hEq
   change E.toFun b=Q.vertex (i-1+1) at hEnd
   exact ⟨b,by simpa only [Nat.sub_add_cancel (by omega: 1≤ i)] using hEnd⟩
end v9
namespace Bi
variable (E: wF G M H K) {r: Fin N} (S: Bi G M r)
lemma B2 (a: Fin N ×Fin N):(S.Nd E).Reaches (E.pairMap a)↔ S.Reaches a:= by
 constructor
 · rintro ⟨Q,hLen,hLast⟩
   have hRange:=E.Bn S.NS r Q
   let L:=Q.MS (E.NH S.NS) r hRange
   refine ⟨L,hLen,?_⟩
   apply E.x4
   have hMap:=Q.sK (E.NH S.NS) r hRange (Q.length-1) (by omega)
   exact hMap.trans hLast
 · rintro ⟨Q,hLen,hLast⟩
   exact ⟨Q.Nd (E.NH S.NS),hLen,congrArg E.pairMap hLast⟩
lemma uM:(S.Nd E).KK=E.Nc S.KK:= by
 apply Subset.antisymm
 · intro a ha
   have hMem:=(S.Nd E).Gk a ha
   obtain ⟨b,hb,hEq⟩:∃b,(b∈S.NS∨ b.swap∈S.NS)∧ E.pairMap b=a:= by
     rcases hMem with hMem|hMem
     · obtain ⟨b,hb,rfl⟩:=mem_image.mp hMem
       exact ⟨b,Or.inl hb,rfl⟩
     · obtain ⟨b,hb,hEq⟩:=mem_image.mp hMem
       exact ⟨b.swap,Or.inr (by simpa using hb),congrArg Prod.swap hEq⟩
   rw [←hEq] at ha ⊢
   apply mem_image.mpr
   refine ⟨b,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩
   rcases (mem_filter.mp ha).2 with hUn|hReach
   · exact Or.inl ⟨fun hm=>hUn.1 ((E.HS b.1 b.2).mpr hm),hb⟩
   · exact Or.inr ((S.B2 E b).mp hReach)
 · intro a ha
   obtain ⟨b,hb,rfl⟩:=mem_image.mp ha
   apply mem_filter.mpr
   refine ⟨mem_univ _,?_⟩
   rcases (mem_filter.mp hb).2 with hUn|hReach
   · exact Or.inl ⟨fun hm=>hUn.1 ((E.HS b.1 b.2).mp hm),
       hUn.2.imp ((E.Jn S.NS b.1 b.2).mpr)
         ((E.Jn S.NS b.2 b.1).mpr)⟩
   · exact Or.inr ((S.B2 E b).mpr hReach)
lemma uN: S.normalized.Nd E=(S.Nd E).normalized:= by
 apply Bi.FJ
 exact (S.uM E).symm
lemma m7 (C: Finset (Fin N ×Fin N))
   (hC:∀u v,(u,v)∈C→ G.Adj u v)
   (hEC:∀u v,(u,v)∈E.Nc C→ H.Adj u v):
   (S.FX C hC).Nd E=(S.Nd E).FX (E.Nc C) hEC:= by
 apply Bi.FJ
 apply Subset.antisymm
 · intro a ha
   change a∈(S.NS∪S.Dq C).image E.pairMap at ha
   obtain ⟨⟨u,v⟩,hLocal,hEq⟩:=mem_image.mp ha
   subst a
   rcases mem_union.mp hLocal with ha|ha
   · exact mem_union_left _ ((E.Jn S.NS u v).mpr ha)
   · obtain ⟨ha,hM,hu,hv⟩:=mem_filter.mp ha
     exact mem_union_right _ (mem_filter.mpr ⟨(E.Jn C u v).mpr ha,
       fun hm=>hM ((E.HS u v).mp hm),
       (S.Aj E).symm ▸mem_image.mpr ⟨u,hu,rfl⟩,
       (S.Aj E).symm ▸mem_image.mpr ⟨v,hv,rfl⟩⟩)
 · intro a ha
   rcases mem_union.mp ha with ha|ha
   · exact E.Eb (show S.NS⊆(S.FX C hC).NS from subset_union_left) ha
   · obtain ⟨ha,hM,hu,hv⟩:=mem_filter.mp ha
     change a∈C.image E.pairMap at ha
     obtain ⟨⟨u,v⟩,hLocal,hEq⟩:=mem_image.mp ha
     subst a
     rw [S.Aj E] at hu hv
     have hu': u∈S.vertices:=by
       obtain ⟨w,hw,hwu⟩:=mem_image.mp hu
       have hh: w=u:=E.injective hwu
       exact hh ▸hw
     have hv': v∈S.vertices:=by
       obtain ⟨w,hw,hwv⟩:=mem_image.mp hv
       have hh: w=v:=E.injective hwv
       exact hh ▸hw
     exact mem_image.mpr ⟨(u,v),mem_union_right _ (mem_filter.mpr ⟨hLocal,
       fun hm=>hM ((E.HS u v).mpr hm),hu',hv'⟩),rfl⟩
end Bi
end Be
end
noncomputable section
namespace Be
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)}
namespace wF
variable (E: wF G M H K)
lemma I3 (A: Finset (Fin N ×Fin N)) (v: Fin N):
   C8 K (E.Nc A) (E.toFun v)↔ C8 M A v:= by
 constructor
 · rintro ⟨a,b,hAB,hM,hV⟩
   change (a,b)∈A.image E.pairMap at hAB
   obtain ⟨⟨u,w⟩,hUW,hEq⟩:=mem_image.mp hAB
   obtain ⟨rfl,rfl⟩:=Prod.mk.inj hEq
   exact ⟨u,w,hUW,(E.HS u w).mp hM,hV.imp (fun h=>E.injective h) (fun h=>E.injective h)⟩
 · exact C8.Nd E A v
end wF
namespace v9
variable (E: wF G M H K) {r: Fin N} (Q: v9 G M r)
lemma Ec (F: Finset (Fin N ×Fin N)):
   (Q.Nd E).Nt (E.Nc F)↔ Q.Nt F:= by
 constructor
 · intro h i hi hMem
   exact h i hi ((E.Jn F _ _).mpr hMem)
 · intro h i hi hMem
   exact h i hi ((E.Jn F _ _).mp hMem)
end v9
namespace Bi
variable (E: wF G M H K) {r: Fin N} (S: Bi G M r)
lemma c3 (F: Finset (Fin N ×Fin N)) (a: Fin N ×Fin N):
   E.pairMap a∈(S.Nd E).CD (E.Nc F)↔ a∈S.CD F:= by
 constructor
 · intro h
   obtain ⟨ha,hm,Q,hLen,hInside,hAvoid,hLast⟩:=mem_filter.mp h
   have hRange:=Q.HC E S.NS hInside
   let L:=Q.MS E r hRange
   refine mem_filter.mpr ⟨(E.Jn S.NS a.1 a.2).mp ha,(E.HS a.1 a.2).mp hm,
     L,hLen,Q.Ct E r hRange S.NS hInside,?_,?_⟩
   · intro i hi hMem
     apply hAvoid i hi
     have hArc:=Q.sK E r hRange i hi
     rw [←hArc]
     exact (E.Jn F _ _).mpr hMem
   · apply E.x4
     exact (Q.sK E r hRange (Q.length-1) (by omega)).trans hLast
 · intro h
   obtain ⟨ha,hm,Q,hLen,hInside,hAvoid,hLast⟩:=mem_filter.mp h
   exact mem_filter.mpr ⟨(E.Jn S.NS a.1 a.2).mpr ha,(E.HS a.1 a.2).mpr hm,
     Q.Nd E,hLen,Q.Ed E S.NS hInside,(Q.Ec E F).mpr hAvoid,
     congrArg E.pairMap hLast⟩
lemma i9 (F: Finset (Fin N ×Fin N)):
   (S.Nd E).CD (E.Nc F)=E.Nc (S.CD F):= by
 apply Subset.antisymm
 · intro a ha
   have hOld:=(mem_filter.mp ha).1
   change a∈S.NS.image E.pairMap at hOld
   obtain ⟨b,hb,rfl⟩:=mem_image.mp hOld
   exact mem_image.mpr ⟨b,(S.c3 E F b).mp ha,rfl⟩
 · intro a ha
   change a∈(S.CD F).image E.pairMap at ha
   obtain ⟨b,hb,rfl⟩:=mem_image.mp ha
   exact (S.c3 E F b).mpr hb
lemma gO (F: Finset (Fin N ×Fin N)) (a: Fin N ×Fin N):
   E.pairMap a∈(S.Nd E).Ip (E.Nc F)↔ a∈S.Ip F:= by
 simp only [Ip,mem_union,mem_filter]
 rw [S.c3 E F a,S.i9 E F]
 change (_∨(E.toFun a.1,E.toFun a.2)∈E.Nc S.NS∧
   ¬K.Adj (E.toFun a.1) (E.toFun a.2)∧
   (E.toFun a.1=E.toFun r∨ C8 K (E.Nc (S.CD F)) (E.toFun a.1))∧
   (E.toFun a.2=E.toFun r∨ C8 K (E.Nc (S.CD F)) (E.toFun a.2)))↔ _
 rw [E.Jn,E.HS,E.I3,E.I3]
 simp only [E.injective.eq_iff]
lemma Ai (F: Finset (Fin N ×Fin N)):
   (S.MT F).Nd E=(S.Nd E).MT (E.Nc F):= by
 apply Bi.FJ
 apply Subset.antisymm
 · intro a ha
   change a∈(S.Ip F).image E.pairMap at ha
   obtain ⟨b,hb,rfl⟩:=mem_image.mp ha
   exact (S.gO E F b).mpr hb
 · intro a ha
   have hOld:=(S.Nd E).pU (E.Nc F) ha
   change a∈S.NS.image E.pairMap at hOld
   obtain ⟨b,hb,rfl⟩:=mem_image.mp hOld
   exact mem_image.mpr ⟨b,(S.gO E F b).mp ha,rfl⟩
end Bi
end Be
end
noncomputable section
namespace Be
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)}
namespace C3
variable (E: wF G M H K) (fallback: Fin N) (Q: C3 H K)
   (hRange:∀i,i≤ 2*Q.length+1→ Q.vertex i∈Set.range E.toFun)
def MS: C3 G M where
 length:=Q.length
 vertex:=fun i=>E.inverse fallback (Q.vertex i)
 injective:=by
   intro i j hi hj hEq
   apply Q.injective i j hi hj
   have h:=congrArg E.toFun hEq
   rw [E.HE fallback _ (hRange i hi),E.HE fallback _ (hRange j hj)] at h
   exact h
 Mu:=by
   intro i hi
   apply (E.LH _ _).mp
   rw [E.HE fallback _ (hRange i (by omega)),E.HE fallback _ (hRange (i+1) (by omega))]
   exact Q.Mu i hi
 MG:=by
   intro i hi
   rw [←E.HS]
   rw [E.HE fallback _ (hRange i (by omega)),E.HE fallback _ (hRange (i+1) (by omega))]
   exact Q.MG i hi
 Ki:=by
   intro v hMatch
   have hGlobal:=(E.HS _ v).mpr hMatch
   rw [E.HE fallback _ (hRange 0 (by omega))] at hGlobal
   exact Q.Ki (E.toFun v) hGlobal
 LP:=by
   intro v hMatch
   have hGlobal:=(E.HS _ v).mpr hMatch
   rw [E.HE fallback _ (hRange (2*Q.length+1) le_rfl)] at hGlobal
   exact Q.LP (E.toFun v) hGlobal
end C3
namespace wF
variable (E: wF G M H K)
lemma l8 (A: Finset (Fin N ×Fin N)) (Q: C3 (Mv H (E.Nc A)) K)
   (i: ℕ) (hi: i≤ 2*Q.length+1): Q.vertex i∈Set.range E.toFun:= by
 by_cases hZero: i=0
 · rw [hZero]
   exact (E.f2 A (Q.Mu 0 (by omega))).1
 · have hEnds:=E.f2 A (Q.Mu (i-1) (by omega))
   simpa only [Nat.sub_add_cancel (by omega: 1≤ i)] using hEnds.2
lemma r5 (fallback: Fin N) (A: Finset (Fin N ×Fin N))
   (hNo:¬Nonempty (C3 (Mv G A) M)):
   ¬Nonempty (C3 (Mv H (E.Nc A)) K):= by
 rintro ⟨Q⟩
 exact hNo ⟨Q.MS (E.NH A) fallback (E.l8 A Q)⟩
end wF
end Be
end
noncomputable section
namespace Be
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)}
namespace G6
variable (E: wF G M H K) (hK: Matching H K) {alpha beta: Fin N}
   (D: G6 G M alpha beta)
def Nd: G6 H K (E.toFun alpha) (E.toFun beta) where
 MG:=hK
 left:=D.left.Nd E
 right:=D.right.Nd E
 NX:=D.NX.Nd E
 inside:=D.NX.Ed E D.left.NS D.inside
 disjoint:=by
   rw [D.left.Aj E,D.right.Aj E]
   apply disjoint_left.mpr
   intro v hv hw
   obtain ⟨a,ha,hav⟩:=mem_image.mp hv
   obtain ⟨b,hb,hbv⟩:=mem_image.mp hw
   have hAB:=E.injective (hav.trans hbv.symm)
   exact disjoint_left.mp D.disjoint ha (hAB.symm ▸hb)
 distinct:=fun h=>D.distinct (E.injective h)
 target:=E.pairMap D.target
 target_mem:=(E.Jn D.right.NS _ _).mpr D.target_mem
 EV:=(E.HS _ _).mpr D.EV
 Nz:=(E.LH _ _).mpr D.Nz
 zV:=fun h=>D.zV ((E.HS _ _).mp h)
 Ck:=by
   have hNo:=E.r5 alpha D.KC D.Ck
   convert hNo using 1
   simp only [KC,wF.Nc,image_union,image_insert,image_singleton]
   rfl
lemma Ee:(D.Nd E hK).KC=E.Nc D.KC:= by
 simp only [KC,Nd,Bi.Nd,wF.Nc,
   image_union,image_insert,image_singleton]
 rfl
end G6
namespace C2
variable (E: wF G M H K) (hK: Matching H K) {alpha beta: Fin N}
   (D: C2 G M alpha beta)
def Nd: C2 H K (E.toFun alpha) (E.toFun beta) where
 data:=D.data.Nd E hK
 Ng:=D.Ng.Nd E
 inside:=D.Ng.Ed E D.data.right.NS D.inside
 index:=D.index
 positive:=D.positive
 bound:=D.bound
 target:=congrArg E.pairMap D.target
lemma HN:(D.Nd E hK).path=D.path.Nd E:= by
 apply v9.Kd
 · rfl
 · funext i
   change (D.data.NX.Nd E).Iy (D.Ng.Nd E) D.index i=
     E.toFun (D.data.NX.Iy D.Ng D.index i)
   unfold v9.Iy
   dsimp only [v9.Nd,v9.JH]
   by_cases h: i≤ 2*D.data.NX.length<;> simp [h]
end C2
namespace v9
variable (E: wF G M H K) {r: Fin N} (Q: v9 G M r)
lemma xF (k n: ℕ):(Q.Nd E).L5 k n=E.Nc (Q.L5 k n):= by
 simp only [L5,wF.Nc,image_image]
 rfl
lemma HO (k: ℕ) (hk: k≤ Q.length):(Q.take k hk).Nd E=(Q.Nd E).take k hk:= by
 apply Kd<;> rfl
end v9
namespace Bi
variable (E: wF G M H K) {r: Fin N} (S: Bi G M r)
end Bi
end Be
end
noncomputable section
namespace Be
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)} {ell: ℕ}
structure Db (E: wF G M H K)
   (S: tI G M ell) (T: tI H K ell): Prop where
 present:∀r R,S.ND.state r=some R→ T.ND.state (E.toFun r)=some (R.Nd E)
 NV:∀u v,S.NV.Adj u v→ T.NV.Adj (E.toFun u) (E.toFun v)
 labels:∀a,a.1∉S.Nm→ T.labels (E.pairMap a)=S.labels a
 owner:∀v,v∉S.Nm→ T.ND.owner (E.toFun v)=(S.ND.owner v).map E.toFun
namespace Db
variable {E: wF G M H K} {S: tI G M ell}
   {T: tI H K ell} (F: Db E S T)
include F in
lemma labelled {r: Fin N} (R: Lp G M r) (hR: S.ND.state r=some R)
   (Q: v9 G M r) (hInside: Q.Nv R.tree.NS)
   (hQ: Q.Mq ell S.labels):(Q.Nd E).Mq ell T.labels:= by
 refine ⟨hQ.1,?_⟩
 intro i hi
 change i< Q.length at hi
 change T.labels (E.pairMap (Q.KA i))≤ i+1
 rw [F.labels (Q.KA i) (S.k7 r R hR _
   (R.tree.EA Q hInside (Q.mem_support (2*i+1) (by omega))))]
 exact hQ.2 i hi
end Db
namespace y7
variable {E: wF G M H K} {S: tI G M ell}
   {T: tI H K ell} (F: Db E S T) {x y: Fin N}
   (R: y7 S x y)
def Nd: y7 T (E.toFun x) (E.toFun y) where
 root:=E.toFun R.root
 state:=R.state.Nd E
 present:=F.present R.root R.state R.present
 J5:=R.J5.Nd E
 Lq:=by change R.state.active.map (fun Q=>Q.Nd E)=some (R.J5.Nd E);rw [R.Lq];rfl
 NX:=R.NX.Nd E
 DL:=⟨R.DL.1,fun i hi=>congrArg E.toFun (R.DL.2 i hi)⟩
 inside:=R.NX.Ed E R.state.tree.NS R.inside
 labelled:=F.labelled R.state R.present R.NX R.inside R.labelled
 NC:=congrArg E.toFun R.NC
 MK:=R.MK
 H9:=R.H9
 bound:=R.bound
 NW:=E.toFun R.NW
 matched:=(E.HS _ _).mpr R.matched
 Kq:=by
   rw [R.NX.B4 E]
   intro h
   obtain ⟨v,hv,hEq⟩:=mem_image.mp h
   exact R.Kq (E.injective hEq ▸hv)
 Kp:=by
   rw [R.NX.B4 E]
   intro h
   obtain ⟨v,hv,hEq⟩:=mem_image.mp h
   exact R.Kp (E.injective hEq ▸hv)
 My:=by
   change R.NX.length+1< T.labels (E.pairMap (y,R.NW))
   rw [F.labels (y,R.NW) (S.HK _ _ R.IY).2]
   exact R.My
 IY:=F.NV x y R.IY
 zV:=fun h=>R.zV ((E.HS x y).mp h)
end y7
namespace Bi
variable (E: wF G M H K) {alpha beta: Fin N}
   (A: Bi G M alpha) (B: Bi G M beta)
lemma pA (x y: Fin N):
   (A.Nd E).Hj (B.Nd E) (E.toFun x) (E.toFun y)=E.Nc (A.Hj B x y):= by
 simp only [Hj,Bi.Nd,wF.Nc,
   image_union,image_insert,image_singleton]
 rfl
end Bi
namespace qF
variable {E: wF G M H K} {S: tI G M ell}
   {T: tI H K ell} (F: Db E S T) {x y: Fin N}
   (R: qF S x y)
def Nd: qF T (E.toFun x) (E.toFun y) where
 ME:=E.toFun R.ME
 L7:=E.toFun R.L7
 left:=R.left.Nd E
 right:=R.right.Nd E
 HJ:=F.present _ _ R.HJ
 GE:=F.present _ _ R.GE
 distinct:=fun h=>R.distinct (E.injective h)
 M1:=by rw [R.left.Aj E];exact mem_image.mpr ⟨x,R.M1,rfl⟩
 head_mem:=by rw [R.right.Aj E];exact mem_image.mpr ⟨y,R.head_mem,rfl⟩
 IY:=F.NV x y R.IY
 zV:=fun h=>R.zV ((E.HS x y).mp h)
 path:={
   length:=R.path.length
   vertex:=fun i=>E.toFun (R.path.vertex i)
   injective:=fun i j hi hj hEq=>R.path.injective i j hi hj (E.injective hEq)
   Mu:=by
     intro i hi
     have hAdj:=(E.Hg (R.left.tree.Hj R.right.tree x y) _ _).mpr (R.path.Mu i hi)
     rw [←R.left.tree.pA E R.right.tree x y] at hAdj
     exact hAdj
   MG:=fun i hi=>(E.HS _ _).trans (R.path.MG i hi)
   Ki:=E.free_map _ R.path.Ki
   LP:=E.free_map _ R.path.LP}
end qF
end Be
end
noncomputable section
namespace Be
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)} {ell: ℕ}
def Dv (E: wF G M H K) (T: tI H K ell)
   (A: Finset (Fin N)) (F: G8 G M) (lab: Fin N ×Fin N→ ℕ)
   (L: SimpleGraph (Fin N)) (hM: Matching G M)
   (hClosed:∀u,u∈A→∀v,M.Adj u v→ v∈A)
   (hAlive:∀u,u∈A→ E.toFun u∉T.Nm)
   (hPresent:∀r R,F.state r=some R→ T.ND.state (E.toFun r)=some (R.Nd E))
   (hVertices:∀r R,F.state r=some R→ R.tree.vertices⊆A)
   (hCover:∀v,v∈A→∀r R,T.ND.state r=some R→ E.toFun v∈R.tree.vertices→
     ∃s U,F.state s=some U∧ E.toFun s=r)
   (hLive:∀u v,L.Adj u v↔ u∈A∧ v∈A∧ T.NV.Adj (E.toFun u) (E.toFun v))
   (hLabels:∀a,a.1∈A→ lab a=T.labels (E.pairMap a))
   (hPos:∀a,1≤ lab a) (hUpper:∀a,lab a≤ ell+1)
   (hComplete: F.qK): tI G M ell where
 MG:=hM
 ND:=F
 labels:=lab
 Nm:=univ\A
 NV:=L
 found:=∅
 MF:=by
   intro u v h
   exact (E.LH u v).mp (T.MF ((hLive u v).mp h).2.2)
 HK:=by
   intro u v h
   obtain ⟨hu,hv,hEdge⟩:=(hLive u v).mp h
   simpa only [mem_sdiff,mem_univ,true_and,not_not] using And.intro hu hv
 HQ:=by
   intro u v hMatch hu
   have huA: u∈A:=by simpa using hu
   apply (hLive u v).mpr
   exact ⟨huA,hClosed u huA v hMatch,T.HQ _ _ ((E.HS u v).mpr hMatch) (hAlive u huA)⟩
 EL:=by
   intro u hu v hMatch
   have huA: u∉A:=(mem_sdiff.mp hu).2
   exact mem_sdiff.mpr ⟨mem_univ _,fun hv=>huA (hClosed v hv u hMatch.symm)⟩
 DQ:=by intro Q hQ;simp at hQ
 Hu:=by simp [Gp]
 DO:=by
   intro r R hR
   apply disjoint_left.mpr
   intro v hv hV
   exact (mem_sdiff.mp hV).2 (hVertices r R hR hv)
 I9:=by
   intro r R hR u v hArc
   have hEnds:=R.tree.Ft u v hArc
   apply (hLive u v).mpr
   exact ⟨hVertices r R hR hEnds.1,hVertices r R hR hEnds.2,
     T.I9 _ _ (hPresent r R hR) _ _ ((E.Jn R.tree.NS u v).mpr hArc)⟩
 Iu:=by
   intro r hFree hr
   have hrA: r∈A:=by simpa using hr
   obtain ⟨R,hR⟩:=T.Iu (E.toFun r) (E.free_map r hFree) (hAlive r hrA)
   obtain ⟨s,U,hU,hSR⟩:=hCover r hrA (E.toFun r) R hR R.tree.MU
   have hSR': s=r:=E.injective hSR
   subst s
   exact ⟨U,hU⟩
 labelled:=by
   intro r R hR Q hQ
   have hGlobal:=T.labelled _ _ (hPresent r R hR) (Q.Nd E)
     (by change R.active.map (fun Q=>Q.Nd E)=some (Q.Nd E);rw [hQ];rfl)
   refine ⟨hGlobal.1,?_⟩
   intro i hi
   rw [hLabels _ (hVertices r R hR (R.tree.EA Q (R.inside Q hQ)
     (Q.mem_support (2*i+1) (by omega))))]
   exact hGlobal.2 i hi
 complete:=hComplete
 positive:=hPos
 upper:=hUpper
lemma gA (E: wF G M H K) (T: tI H K ell)
   (A: Finset (Fin N)) (F: G8 G M) (lab: Fin N ×Fin N→ ℕ)
   (L: SimpleGraph (Fin N)) (hM: Matching G M)
   (hClosed:∀u,u∈A→∀v,M.Adj u v→ v∈A)
   (hAlive:∀u,u∈A→ E.toFun u∉T.Nm)
   (hPresent:∀r R,F.state r=some R→ T.ND.state (E.toFun r)=some (R.Nd E))
   (hVertices:∀r R,F.state r=some R→ R.tree.vertices⊆A)
   (hCover:∀v,v∈A→∀r R,T.ND.state r=some R→ E.toFun v∈R.tree.vertices→
     ∃s U,F.state s=some U∧ E.toFun s=r)
   (hLive:∀u v,L.Adj u v↔ u∈A∧ v∈A∧ T.NV.Adj (E.toFun u) (E.toFun v))
   (hLabels:∀a,a.1∈A→ lab a=T.labels (E.pairMap a))
   (hPos:∀a,1≤ lab a) (hUpper:∀a,lab a≤ ell+1)
   (hComplete: F.qK):
   Db E (Dv E T A F lab L hM hClosed hAlive hPresent hVertices
     hCover hLive hLabels hPos hUpper hComplete) T:= by
 refine ⟨hPresent,fun u v h=>((hLive u v).mp h).2.2,?_,?_⟩
 · intro a ha
   exact (hLabels a (by simpa [Dv] using ha)).symm
 · intro v hv
   have hvA: v∈A:=by simpa [Dv] using hv
   change T.ND.owner (E.toFun v)=(F.owner v).map E.toFun
   cases hOwner: F.owner v with
   | some r =>
     obtain ⟨R,hR,hV⟩:=(F.KP r v).mp hOwner
     have hPhys: E.toFun v∈(R.Nd E).tree.vertices:=by
       rw [R.Aj E];exact mem_image.mpr ⟨v,hV,rfl⟩
     exact (T.ND.KP _ _).mpr ⟨R.Nd E,hPresent r R hR,hPhys⟩
   | none =>
     change T.ND.owner (E.toFun v)=none
     cases hPhysOwner: T.ND.owner (E.toFun v) with
     | none => rfl
     | some r =>
       obtain ⟨R,hR,hV⟩:=(T.ND.KP r _).mp hPhysOwner
       obtain ⟨s,U,hU,hSR⟩:=hCover v hvA r R hR hV
       subst r
       have hEq: U.Nd E=R:=Option.some.inj ((hPresent s U hU).symm.trans hR)
       rw [←hEq,U.Aj E] at hV
       obtain ⟨u,hu,hUV⟩:=mem_image.mp hV
       have hUV': u=v:=E.injective hUV
       have hLocalOwner: F.owner v=some s:=(F.KP s v).mpr ⟨U,hU,hUV' ▸hu⟩
       rw [hOwner] at hLocalOwner
       cases hLocalOwner
end Be
end
noncomputable section
namespace Be
structure Ln where
 neighbors: Finset ℕ
 Jf: Option ℕ
 labels: ℕ→ ℕ
 ignored: Finset ℕ
 Nm: Bool
 Md: Option ℕ
 L8: Option tF
namespace Ln
instance: Inhabited Ln:=⟨⟨∅,none,fun _=>1,∅,false,none,none⟩⟩
def static (z: Ln): J2:=(z.neighbors,z.Jf)
def leader (j: ℕ) (z: Ln): ℕ:=
 z.L8.elim (IH j z.Jf) tF.leader
end Ln
abbrev IO:=Finset (ℕ ×Ln)
namespace IO
def keys (D: IO): Finset ℕ:=D.image Prod.fst
def node (D: IO) (j: ℕ): Ln:=(lookup D j).getD default
def GM (D: IO): y6:=D.image (fun z=>(z.1,z.2.static))
def history (D: IO): y6:=D.GM∪
 D.biUnion (fun z=>z.2.L8.elim ∅ (fun A=>A.history))
lemma vZ (D: IO): D.GM.keys=D.keys:= by
 simp only [y6.keys,GM,keys,image_image]
 rfl
lemma rP (D: IO): D.keys⊆D.history.keys:= by
 rw [←D.vZ]
 exact image_subset_image subset_union_left
lemma pF (D: IO) (j: ℕ) (z: Ln) (hZ:(j,z)∈D)
   (A: tF) (hA: z.L8=some A): A.history⊆D.history:= by
 intro x hx
 apply mem_union_right
 apply mem_biUnion.mpr
 exact ⟨(j,z),hZ,by simp only [hA,Option.elim_some];exact hx⟩
def alive (D: IO): Finset (Fin D.history.keys.card):=
 univ.filter (fun v=>D.history.identity v∈D.keys∧(D.node (D.history.identity v)).Nm=false)
def labels (D: IO) (ell: ℕ) (a: Fin D.history.keys.card ×Fin D.history.keys.card): ℕ:=
 if D.history.identity a.1∈D.keys then (D.node (D.history.identity a.1)).labels (D.history.identity a.2)
 else ell+1
def NV (D: IO): SimpleGraph (Fin D.history.keys.card) where
 Adj u v:=D.history.graph.Adj u v∧ u∈D.alive∧ v∈D.alive∧
   D.history.identity v∉(D.node (D.history.identity u)).ignored∧
   D.history.identity u∉(D.node (D.history.identity v)).ignored
 symm:=⟨by rintro u v ⟨hG,hu,hv,hUV,hVU⟩;exact ⟨hG.symm,hv,hu,hVU,hUV⟩⟩
 loopless:=⟨fun _ h=>h.1.ne rfl⟩
end IO
end Be
end
noncomputable section
namespace Be
variable {N: ℕ}
namespace tE
def K7 (G: SimpleGraph (Fin N)): tE G 1 where
 leader:= id
 fixed:= fun _=> rfl
 connected:= by
   intro u v heq
   change u= v at heq
   subst v
   exact SimpleGraph.Reachable.refl _
 small:= by intro v;simp only [id_eq,filter_eq',mem_univ,if_true,card_singleton,le_refl]
lemma p2 (G: SimpleGraph (Fin N)):
   (K7 G).Lv (fun _ _=> True) (fun _ _ _=> trivial)= G:= by
 ext u v
 constructor
 · rintro ⟨_,_,_,a,b,ha,hb,hab,_⟩
   exact ha ▸hb ▸hab
 · intro h
   exact ⟨rfl,rfl,h.ne,u,v,rfl,rfl,h,trivial⟩
noncomputable def Hv (G M: SimpleGraph (Fin N)) (hM: Matching G M)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids): tE G 2:=
 (K7 G).merge (fun _ _=> True) (fun _ _ _=> trivial) M
   (by rw [p2];exact hM) ids hi
lemma q7 (G M: SimpleGraph (Fin N)) (hM: Matching G M)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (v: Fin N):
   (Hv G M hM ids hi).leader v= representative ids (Ni ids hi M) v:= rfl
lemma t6 (G M: SimpleGraph (Fin N)) (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (out: Fin N→ Option ℕ) (hout: ReportsMatching G ids out M) (v: Fin N):
   IH (ids v) (out v)= ids ((Hv G M hout.1 ids hi).leader v):=
 qE G M ids hi out hout v
end tE
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S: tI G M ell} {x y: Fin N} {R: y7 S x y}
namespace G8
def M7 (F: G8 G M) (e: Fin N ×Fin N): Prop:= F.Mn (fun _ R=> R.tree.Reaches e)
end G8
lemma Bb.yF (A: Bb R) (e: Fin N ×Fin N)
   (h: S.ND.M7 e): A.Nj.ND.M7 e:= by
 cases A with
 | single hOwner =>
   apply G8.t8 S.ND _ (fun _ B=> B.tree.Reaches e) R.state _ R.present rfl _ h
   intro hp
   apply Bi.vN
   exact R.state.tree.Ij _ subset_union_left e hp
 | inactive D B hB hAT hBT hStem hTarget hInactive =>
   apply G8.t9 S.ND _ (fun _ B=> B.tree.Reaches e)
     D.distinct R.state B R.present hB _ _ rfl _ _ h
   · intro hp
     left
     apply Bi.fJ
     apply D.left.Ij D.JM D.BY
     simpa only [hAT] using hp
   · intro hp
     have hc: D.right.qK:= by rw [←hBT];exact S.complete _ B hB
     have hr: D.right.Reaches e:= by simpa only [hBT] using hp
     rcases D.pY hc e hr with hl|hr
     · exact Or.inl (Bi.fJ _ _ _ _ hl)
     · exact Or.inr (Bi.fJ _ _ _ _ hr)
 | active D B hB hAT hBT hStem hTarget hActive =>
   apply G8.t9 S.ND _ (fun _ B=> B.tree.Reaches e)
     D.data.distinct R.state B R.present hB _ _ rfl _ _ h
   · intro hp
     left
     apply Bi.fJ
     apply D.data.left.Ij _ (Classical.choice D.transfer).NL
     simpa only [hAT] using hp
   · intro hp
     have hc: D.data.right.qK:= by rw [←hBT];exact S.complete _ B hB
     have hr: D.data.right.Reaches e:= by simpa only [hBT] using hp
     rcases D.pY hc e hr with hl|hr
     · exact Or.inl (Bi.fJ _ _ _ _ hl)
     · exact Or.inr (Bi.fJ _ _ _ _ hr)
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma Lp.tL {r: Fin N} (A: Lp G M r) (P: v9 G M r)
   (hactive: A.active= some P) (i: ℕ) (hi: i< P.length): A.tree.Reaches (P.KA i):= by
 apply A.tree.EE _ _ (P.HR i hi)
 have h:= A.inside P hactive (2*i+1) (by omega)
 simpa only [v9.KA,show 2*i+1+1=2*i+2 by omega] using h
lemma M2.In {mode: Bool} {es: List (Fin N ×Fin N)} (h: M2 mode es S T): S.Nm ⊆T.Nm:= by
 induction h with
 | nil S => exact subset_refl _
 | cons step rest ih => exact step.In.trans ih
lemma M2.q9 {mode: Bool} {es: List (Fin N ×Fin N)} (h: M2 mode es S T):
   ∀a b: Fin N ×Fin N,¬M.Adj a.2 b.2→ a.1∉ T.Nm→
     S.ND.JV a b→ T.ND.JV a b:= by
 induction h with
 | nil S => intros;assumption
 | cons step rest ih =>
   intro a b hM halive hs
   apply ih a b hM halive
   exact step.q9 a b hM (fun he=> halive (rest.In he)) hs
lemma tI.zA.IX (S: tI G M ell) (hS: S.zA) (limit: ℕ):
   (S.IX limit).zA:= by
 intro r R hR u v huv hu hv hM
 change (S.ND.state r).map (fun R=> R.IX limit)= some R at hR
 obtain ⟨Q,hQ,hQR⟩:= Option.map_eq_some_iff.mp hR
 rw [←hQR] at hu hv ⊢
 exact hS r Q hQ u v huv hu hv hM
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
namespace G8
def G4 (F: G8 G M) (a: ℕ→ Fin N ×Fin N) (n k: ℕ)
   (E: Finset (Fin N ×Fin N)): Prop:=
 F.Ny (a 0) k E∧∀i,i+1< n→ F.JV (a i) (a (i+1)).swap
end G8
lemma M3.Ds {mode: Bool} {x y: Fin N} (h: M3 mode x y S T)
   (a: ℕ→ Fin N ×Fin N) (n k: ℕ) (hn: 0< n) (E: Finset (Fin N ×Fin N))
   (hE:∀e∈ E,∃i,i< n∧(e= a i∨ e=(a i).swap))
   (hmatched:∀i,i< n→ M.Adj (a i).1 (a i).2)
   (hUnmatched:∀i,i+1< n→¬M.Adj (a i).2 (a (i+1)).1)
   (halive:∀i,i< n→(a i).1∉ T.Nm)
   (hs: S.ND.G4 a n k E): T.ND.G4 a n k E:= by
 have hfirst:∃r,S.ND.Mm r (a 0).1:= by
   obtain ⟨r,R,hR,htrack⟩:= hs.1
   exact ⟨r,R,hR,R.CU htrack⟩
 have htogether:= S.ND.gG S.MG a n hs.2 hfirst hmatched 0 hn E hE
 constructor
 · exact h.A1 (a 0) k E htogether (halive 0 hn) hs.1
 · intro i hi
   exact h.q9 (a i) (a (i+1)).swap (hUnmatched i hi) (halive i (by omega)) (hs.2 i hi)
lemma M2.Ds {mode: Bool} {es: List (Fin N ×Fin N)} (h: M2 mode es S T)
   (a: ℕ→ Fin N ×Fin N) (n k: ℕ) (hn: 0< n) (E: Finset (Fin N ×Fin N))
   (hE:∀e∈ E,∃i,i< n∧(e= a i∨ e=(a i).swap))
   (hmatched:∀i,i< n→ M.Adj (a i).1 (a i).2)
   (hUnmatched:∀i,i+1< n→¬M.Adj (a i).2 (a (i+1)).1):
   (∀i,i< n→(a i).1∉ T.Nm)→
     S.ND.G4 a n k E→ T.ND.G4 a n k E:= by
 induction h with
 | nil S => intro halive hs;exact hs
 | cons step rest ih =>
   intro halive hs
   apply ih halive
   apply step.Ds a n k hn E hE hmatched hUnmatched _ hs
   intro i hi he
   exact halive i hi (rest.In he)
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
namespace G8
lemma G4.map {F: G8 G M} (a: ℕ→ Fin N ×Fin N) (n k: ℕ)
   (E: Finset (Fin N ×Fin N)) (hs: F.G4 a n k E)
   (f:∀r,Lp G M r→ Lp G M r)
   (hV:∀r R,(f r R).tree.vertices= R.tree.vertices)
   (hActive:∀r R,(f r R).active= R.active)
   (hArcs:∀r R,R.tree.NS ⊆(f r R).tree.NS):(F.LU f hV).G4 a n k E:= by
 constructor
 · exact F.Lc f hV (a 0) k E (fun r R h=> R.v1 (f r R) (hActive r R) h) hs.1
 · intro i hi
   apply F.Hw (fun _ R=> R.tree.Mo (a i) (a (i+1)).swap) f hV _ (hs.2 i hi)
   intro r R hp
   exact R.tree.FT (f r R).tree (hArcs r R) (a i) (a (i+1)).swap hp
end G8
namespace tI
variable (S: tI G M ell) (a: ℕ→ Fin N ×Fin N) (n k: ℕ) (E: Finset (Fin N ×Fin N))
lemma IZ (limit: ℕ) (hs: S.ND.G4 a n k E):
   (S.IX limit).ND.G4 a n k E:=
 hs.map a n k E (fun _ R=> R.IX limit) (fun _ _=> rfl) (fun _ _=> rfl) (fun _ _=> subset_refl _)
lemma Ka (limit: ℕ) (hs: S.ND.G4 a n k E):
   (S.rC limit).ND.G4 a n k E:=
 hs.map a n k E (fun _ R=> R.rC limit) (fun _ _=> rfl) (fun _ _=> rfl) (fun _ _=> subset_refl _)
lemma FA (hs: S.ND.G4 a n k E): S.z9.ND.G4 a n k E:= by
 apply hs.map a n k E (fun _ R=> R.z8 S.NV S.MF)
   (fun _ R=> R.fA S.NV S.MF) (fun _ _=> rfl)
 intro r R e he
 apply Bi.Cl
 exact mem_union_left _ he
end tI
lemma M2.lP {S T: tI G M ell} {mode: Bool} {es: List (Fin N ×Fin N)}
   (h: M2 mode es S T):∀e: Fin N ×Fin N,e.1∉ T.Nm→ S.ND.IP e→ T.ND.IP e:= by
 induction h with
 | nil S => intros;assumption
 | cons step rest ih =>
   intro e halive hs
   apply ih e halive
   exact step.lP e (fun he=> halive (rest.In he)) hs
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma tI.fB (G M: SimpleGraph (Fin N)) (hM: Matching G M) (ell: ℕ):
   (tI.initial G M hM ell).zA:= by
 intro r R hR u v huv hu hv hUnmatched
 change (if h:∀w,¬M.Adj r w then some (Lp.initial G M r h) else none)= some R at hR
 split_ifs at hR with hf
 cases Option.some.inj hR
 have hur: u= r:= by simpa [Lp.initial,Bi.vertices,Bi.initial] using hu
 have hvr: v= r:= by simpa [Lp.initial,Bi.vertices,Bi.initial] using hv
 exact (huv.ne (hur.trans hvr.symm)).elim
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
namespace G8
def Bg (F: G8 G M) (e: Fin N ×Fin N) (k: ℕ): Prop:=
 F.Mn (fun _ R=> R.modified= true∧ R.Ny e k ∅)
lemma gX {F H: G8 G M} (hBack: Df F H)
   (e: Fin N ×Fin N) (k: ℕ) (hs: F.Bg e k) (ht: H.Ny e k ∅): H.Bg e k:= by
 obtain ⟨r,R,hR,htrack⟩:= ht
 cases hm: R.modified with
 | true => exact ⟨r,R,hR,hm,htrack⟩
 | false =>
   obtain ⟨Q,hQ,hQm,hRA,hRH,hRE⟩:= hBack r R hR hm
   have hQtrack:= R.v1 Q hRA.symm htrack
   obtain ⟨s,A,hA,hAm,hAtrack⟩:= hs
   have hsr:= F.BE s r e.1 ⟨A,hA,A.CU hAtrack⟩ ⟨Q,hQ,Q.CU hQtrack⟩
   have hex:∃A,F.state s= some A∧ A.modified= true:=⟨A,hA,hAm⟩
   rw [hsr] at hex
   obtain ⟨B,hB,hBm⟩:= hex
   cases Option.some.inj (hB.symm.trans hQ)
   rw [hQm] at hBm
   cases hBm
end G8
variable {S T: tI G M ell}
lemma M2.DE {mode: Bool} {es: List (Fin N ×Fin N)} (h: M2 mode es S T):
   ∀e: Fin N ×Fin N,∀k,e.1∉ T.Nm→ S.ND.Ny e k ∅→ T.ND.Ny e k ∅:= by
 induction h with
 | nil S => intros;assumption
 | cons step rest ih =>
   intro e k halive hs
   apply ih e k halive
   apply step.A1 e k ∅ _ (fun he=> halive (rest.In he)) hs
   intro r B hB hv f hf
   simp at hf
lemma M2.vK {mode: Bool} {es: List (Fin N ×Fin N)} (h: M2 mode es S T)
   (e: Fin N ×Fin N) (k: ℕ) (halive: e.1∉ T.Nm) (hs: S.ND.Bg e k): T.ND.Bg e k:= by
 apply G8.gX h.CX e k hs
 obtain ⟨r,R,hR,hm,htrack⟩:= hs
 exact h.DE e k halive ⟨r,R,hR,htrack⟩
lemma M3.o6 {mode: Bool} {x y: Fin N} (h: M3 mode x y S T)
   (e: Fin N ×Fin N) (hdrop: T.labels e< S.labels e): T.ND.Bg e (T.labels e-1):= by
 cases h with
 | augmentation R hflag => change S.labels e< S.labels e at hdrop;omega
 | skip hNo hNoExt => omega
 | extension hmode R hNo A =>
   have hstrict: A.Nf.Nl S.labels e< S.labels e:= by rwa [←A.LO]
   obtain ⟨i,hi,hie,heq⟩:= k8 A.Nf S.labels e hstrict
   obtain ⟨B,hB,hactive,hm,he,hh⟩:= A.EG
   have hlabel: A.Nj.labels e= i+1:= by rw [A.LO];exact heq
   refine ⟨R.root,B,hB,hm,A.Nf,i,hactive,hi,?_,hie,?_⟩
   · rw [hlabel];omega
   · intro j hj hmem;simp at hmem
lemma M2.o6 {mode: Bool} {es: List (Fin N ×Fin N)} (h: M2 mode es S T):
   ∀e: Fin N ×Fin N,e.1∉ T.Nm→ T.labels e< S.labels e→ T.ND.Bg e (T.labels e-1):= by
 induction h with
 | nil S => intros;omega
 | @cons x y es S U T step rest ih =>
   intro e halive hdrop
   by_cases hlast: T.labels e< U.labels e
   · exact ih e halive hlast
   · have heq: T.labels e= U.labels e:= by have hm:=rest.Jj e;omega
     have hfirst: U.labels e< S.labels e:= by omega
     have hnew:= step.o6 e hfirst
     have hfinal:= rest.vK e (U.labels e-1) halive hnew
     rwa [←heq] at hfinal
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma M3.Bv {x y: Fin N} (h: M3 false x y S T): T.labels= S.labels:= by
 cases h with
 | augmentation R hflag => rfl
 | extension hmode R hNo A => cases hmode
 | skip hNo hNoExt => rfl
lemma M2.Bv {es: List (Fin N ×Fin N)} (h: M2 false es S T): T.labels= S.labels:= by
 induction h with
 | nil S => rfl
 | cons step rest ih => exact ih.trans step.Bv
namespace tI
variable (S: tI G M ell) (e: Fin N ×Fin N) (k: ℕ)
lemma ED (limit: ℕ) (hs: S.ND.Bg e k):
   (S.rC limit).ND.Bg e k:= by
 apply S.ND.Hw _ (fun _ R=> R.rC limit) (fun _ _=> rfl) _ hs
 intro r R hp
 exact ⟨hp.1,R.v1 _ rfl hp.2⟩
lemma sJ (hs: S.ND.Bg e k): S.Dk.ND.Bg e k:= by
 apply S.ND.Hw _ (fun _ R=> R.zS) _ _ hs
 · intro r R;unfold Lp.zS;split_ifs<;> rfl
 · intro r R hp
   have hflag:(R.NU|| R.modified)= true:= by simp [hp.1]
   simpa only [Lp.zS,if_pos hflag] using hp
lemma yD (hs: S.ND.Bg e k): S.z9.ND.Bg e k:= by
 apply S.ND.Hw _ (fun _ R=> R.z8 S.NV S.MF)
   (fun _ R=> R.fA S.NV S.MF) _ hs
 intro r R hp
 exact ⟨hp.1,R.v1 _ rfl hp.2⟩
end tI
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma M3.yF {mode: Bool} {x y: Fin N} (h: M3 mode x y S T)
   (e: Fin N ×Fin N) (halive: e.1∉ T.Nm) (hs: S.ND.M7 e): T.ND.M7 e:= by
 cases h with
 | augmentation A hflag =>
   obtain ⟨r,R,hR,he⟩:= hs
   have hmem: e.1∈ R.tree.vertices:=(R.tree.yG e he).1
   by_cases hra: r= A.ME
   · subst r
     have hRA: R= A.left:= Option.some.inj (hR.symm.trans A.HJ)
     subst R
     exact (halive (mem_union_right _ (mem_union_left _ hmem))).elim
   · by_cases hrb: r= A.L7
     · subst r
       have hRB: R= A.right:= Option.some.inj (hR.symm.trans A.GE)
       subst R
       exact (halive (mem_union_right _ (mem_union_right _ hmem))).elim
     · refine ⟨r,R,?_,he⟩
       change (if r∈({A.ME,A.L7}:Finset (Fin N)) then none else S.ND.state r)= some R
       simp only [mem_insert,mem_singleton,hra,hrb,or_self,if_false]
       exact hR
 | extension hmode R hNo A => exact A.yF e hs
 | skip hNo hNoExt => exact hs
lemma M2.yF {mode: Bool} {es: List (Fin N ×Fin N)} (h: M2 mode es S T):
   ∀e: Fin N ×Fin N,e.1∉ T.Nm→ S.ND.M7 e→ T.ND.M7 e:= by
 induction h with
 | nil S => intros;assumption
 | cons step rest ih =>
   intro e halive hs
   exact ih e halive (step.yF e (fun he=> halive (rest.In he)) hs)
lemma Bf.yF (h: Bf S T)
   (e: Fin N ×Fin N) (halive: e.1∉ T.Nm) (hs: S.ND.M7 e): T.ND.M7 e:= by
 cases h with
 | edge mode x y step => exact step.yF e halive hs
 | begin limit => exact S.ND.Hw _ (fun _ R=> R.IX limit) (fun _ _=> rfl) (fun _ _ h=> h) hs
 | hold limit => exact S.ND.Hw _ (fun _ R=> R.rC limit) (fun _ _=> rfl) (fun _ _ h=> h) hs
 | backtrack =>
   apply S.ND.Hw _ (fun _ R=> R.zS) _ _ hs
   · intro r R;unfold Lp.zS;split_ifs<;> rfl
   · intro r R hp;unfold Lp.zS;split_ifs<;> exact hp
 | includeEdges =>
   exact S.ND.Hw _ (fun _ R=> R.z8 S.NV S.MF)
     (fun _ R=> R.fA S.NV S.MF)
     (fun _ R hp=> R.tree.fJ _ _ e hp) hs
 | erase E hM hMemory => exact hs
 | idle => exact hs
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma tI.o3 (S: tI G M ell) (hInternal: S.zA)
   {r: Fin N} (A: Lp G M r) (hA: S.ND.state r= some A)
   (u v: Fin N) (huv: S.NV.Adj u v) (hu: u∈ A.tree.vertices) (hv: v∈ A.tree.vertices):
   (Mv G A.tree.NS).Adj u v:= by
 by_cases hm: M.Adj u v
 · exact A.tree.kW S.MG u v hm hu
 · exact ⟨S.MF huv,Or.inl (hInternal r A hA u v huv hu hv hm)⟩
lemma G8.AJ (F: G8 G M) (e: Fin N ×Fin N)
   {r: Fin N} (A: Lp G M r) (hA: F.state r= some A) (heA: e.1∈ A.tree.vertices)
   (h: F.M7 e): A.tree.Reaches e:= by
 obtain ⟨s,B,hB,heB⟩:= h
 have hrs:= F.BE r s e.1 ⟨A,hA,heA⟩ ⟨B,hB,(B.tree.yG e heB).1⟩
 subst s
 have hBA: B= A:= Option.some.inj (hB.symm.trans hA)
 subst B
 exact heB
lemma Lp.IF {r: Fin N} (A: Lp G M r) (e: Fin N ×Fin N) (k: ℕ)
   (E: Finset (Fin N ×Fin N)) (h: A.Ny e k E): A.Ny e k ∅:= by
 obtain ⟨P,i,hP,hi,hik,hie,havoid⟩:= h
 refine ⟨P,i,hP,hi,hik,hie,?_⟩
 intro j hj hmem;simp at hmem
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G H M: SimpleGraph (Fin N)}
namespace v9
variable {r: Fin N} (P: v9 G M r)
lemma B6 (hM: Matching H M) (e: Fin N ×Fin N) (heM: M.Adj e.1 e.2)
   (hhit: e.1∈ P.support∨ e.2∈ P.support):
   ∃i,i< P.length∧(P.KA i= e∨ P.KA i= e.swap):= by
 have hex:∃v,v∈ P.support∧ v∈ s(e.1,e.2):= by
   rcases hhit with h|h
   · exact ⟨e.1,h,Sym2.mem_mk_left _ _⟩
   · exact ⟨e.2,h,Sym2.mem_mk_right _ _⟩
 obtain ⟨v,hv,hve⟩:= hex
 have hne: v≠ r:= by
   intro heq
   rw [heq] at hve
   rcases Sym2.mem_iff.mp hve with ht|hh
   · exact P.L9 e.2 (ht ▸heM)
   · exact P.L9 e.1 (hh ▸heM.symm)
 obtain ⟨i,hi,hvi⟩:= P.v7 v hv hne
 have he:= m9 hM _ _ (M.mem_edgeSet.mpr (P.HR i hi)) (M.mem_edgeSet.mpr heM) v hvi hve
 refine ⟨i,hi,?_⟩
 rcases Sym2.eq_iff.mp he with he|he
 · exact Or.inl (Prod.ext he.1 he.2)
 · exact Or.inr (Prod.ext he.1 he.2)
end v9
namespace Bi
variable {r: Fin N} (A: Bi G M r) (P: v9 G M r)
lemma cI (hP: P.Nv A.NS) (i: ℕ) (hi: i+1< P.length)
   (hEdge: G.Adj (P.vertex (2*P.length)) (P.vertex (2*i+2)))
   (hUnmatched:¬M.Adj (P.vertex (2*P.length)) (P.vertex (2*i+2)))
   (hCache:(P.vertex (2*P.length),P.vertex (2*i+2))∈ A.NS):
   A.Reaches (P.KA (P.length-1)).swap:= by
 let Q:= P.take (i+1) (by omega)
 let L:= Q.Kt A.NS (P.JJ A.NS hP (i+1) (by omega))
 have hLastArc:(P.vertex (2*P.length-1),P.vertex (2*P.length))∈ A.NS:= by
   have h:= hP (2*P.length-1) (by omega)
   rwa [show 2*P.length-1+1=2*P.length by omega] at h
 have hBridge:(Mv G A.NS).Adj (L.vertex (2*L.length)) (P.vertex (2*P.length)):= by
   change G.Adj (P.vertex (2*(i+1))) (P.vertex (2*P.length))∧ _
   rw [show 2*(i+1)=2*i+2 by omega]
   exact ⟨hEdge.symm,Or.inr hCache⟩
 have hMatch: M.Adj (P.vertex (2*P.length)) (P.vertex (2*P.length-1)):= by
   have h:= P.HR (P.length-1) (by omega)
   have ht: 2*(P.length-1)+1=2*P.length-1:= by omega
   have hh: 2*(P.length-1)+2=2*P.length:= by omega
   rw [ht,hh] at h
   exact h.symm
 have hGMatch:(Mv G A.NS).Adj (P.vertex (2*P.length)) (P.vertex (2*P.length-1)):=
   ⟨(A.valid _ _ hLastArc).symm,Or.inr hLastArc⟩
 have hNo:¬M.Adj (L.vertex (2*L.length)) (P.vertex (2*P.length)):= by
   change ¬M.Adj (P.vertex (2*(i+1))) (P.vertex (2*P.length))
   rw [show 2*(i+1)=2*i+2 by omega]
   exact fun h=> hUnmatched h.symm
 have hFresh (j: ℕ) (hj: 2*(i+1)< j) (hj': j≤ 2*P.length): P.vertex j∉ L.support:= by
   intro hv
   obtain ⟨k,hk,he⟩:= mem_image.mp hv
   have hk': k≤ 2*(i+1):= by have h:=mem_range.mp hk;change k< 2*(i+1)+1 at h;omega
   have heq:= P.injective k j (by omega) hj' he
   omega
 let R:= L.Fq (P.vertex (2*P.length)) (P.vertex (2*P.length-1)) hBridge hGMatch hNo hMatch
   (hFresh _ (by omega) le_rfl) (hFresh _ (by omega) (by omega))
 refine ⟨R,by change 0< L.length+1;omega,?_⟩
 have hlast:= L.tM (P.vertex (2*P.length)) (P.vertex (2*P.length-1)) hBridge hGMatch hNo hMatch
   (hFresh _ (by omega) le_rfl) (hFresh _ (by omega) (by omega))
 change R.KA L.length= _ at hlast
 change R.KA (L.length+1-1)= _
 rw [Nat.add_sub_cancel,hlast]
 apply Prod.ext<;> change P.vertex _= P.vertex _<;> congr 1<;> omega
end Bi
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell} {x y: Fin N}
lemma M2.jT {mode: Bool} {es: List (Fin N ×Fin N)}
   (h: M2 mode es S T) (R: y7 T x y) (hm: R.state.modified= false):
   ∃Q: y7 S x y,Q.root= R.root:= by
 obtain ⟨B,hB,hBm,hBA,hBH,hBE⟩:= h.CX R.root R.state R.present hm
 obtain ⟨C,hC,hCm,hv,hg,hcache⟩:= h.lY R.root R.state R.present hm
 have hCB: C= B:= Option.some.inj (hC.symm.trans hB)
 subst C
 have hInside: R.NX.Nv B.tree.NS:= by
   let P:=(R.NX.Kt R.state.tree.NS R.inside).NM hg
   exact S.complete R.root B hB P
 have hLabel: R.NX.Mq ell S.labels:= by
   refine ⟨R.labelled.1,?_⟩
   intro i hi
   have htail:(R.NX.KA i).1∈ R.state.tree.vertices:=
     R.state.tree.EA R.NX R.inside (R.NX.mem_support (2*i+1) (by omega))
   have heq:= h.i6 R.root R.state R.present hm (R.NX.KA i) htail
   have hl:= R.labelled.2 i hi
   change S.labels (R.NX.KA i)≤ i+1
   change T.labels (R.NX.KA i)≤ i+1 at hl
   rw [←heq]
   exact hl
 let Q: y7 S x y:=
   { root:= R.root
     state:= B
     present:= hB
     J5:= R.J5
     Lq:= hBA.symm.trans R.Lq
     NX:= R.NX
     DL:= R.DL
     inside:= hInside
     labelled:= hLabel
     NC:= R.NC
     MK:= hBH.symm.trans R.MK
     H9:= hBE.symm.trans R.H9
     bound:= R.bound
     NW:= R.NW
     matched:= R.matched
     Kq:= R.Kq
     Kp:= R.Kp
     My:= R.My.trans_le (h.Jj (y,R.NW))
     IY:= h.MF R.IY
     zV:= R.zV}
 exact ⟨Q,rfl⟩
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   (S: tI G M ell) {r: Fin N}
lemma a6 (A: Lp G M r) (hA: S.ND.state r= some A)
   (P Z: v9 G M r) (hactive: A.active= some P) (hext: P.M4 Z)
   (hheld: A.NU= false) (hextended: A.extended= false) (hbound: Z.length≤ ell)
   (hknown:∀i,i< 2*(Z.length-1)→(Z.vertex i,Z.vertex (i+1))∈ A.tree.NS)
   (hlive:∀i,i< Z.length→ S.NV.Adj (Z.vertex (2*i)) (Z.vertex (2*i+1)))
   (hbad:∃i,i< Z.length∧ i+1< S.labels (Z.KA i)):
   ∃(i: ℕ),i< Z.length∧∃R: y7 S (Z.vertex (2*i)) (Z.vertex (2*i+1)),
     R.root= r∧ R.NX.length= i:= by
 let j:= Nat.find hbad
 have hj: j< Z.length∧ j+1< S.labels (Z.KA j):= Nat.find_spec hbad
 have hsmall (i: ℕ) (hi: i< j): S.labels (Z.KA i)≤ i+1:= by
   have hn:= Nat.find_min hbad hi
   omega
 have hPj: P.length≤ j:= by
   by_contra hn
   have hjP: j< P.length:= by omega
   have he: Z.KA j= P.KA j:= Prod.ext
     (hext.2 (2*j+1) (by omega)) (hext.2 (2*j+2) (by omega))
   have hl:=(S.labelled r A hA P hactive).2 j hjP
   change S.labels (P.KA j)≤ j+1 at hl
   rw [←he] at hl
   omega
 let Q:= Z.take j hj.1.le
 have hPQ: P.M4 Q:=⟨hPj,fun i hi=> hext.2 i hi⟩
 have hQinside: Q.Nv A.tree.NS:= by
   intro i hi
   exact hknown i (by change i< 2*j at hi;omega)
 have hQlabel: Q.Mq ell S.labels:=⟨by change j≤ ell;omega,fun i hi=> hsmall i hi⟩
 have hfresh (k: ℕ) (hk: 2*j< k) (hk': k≤ 2*Z.length): Z.vertex k∉ Q.support:= by
   intro hmem
   obtain ⟨i,hi,he⟩:= mem_image.mp hmem
   have hi': i≤ 2*j:= by have h:=mem_range.mp hi;change i< 2*j+1 at h;omega
   have heq:= Z.injective i k (by omega) hk' he
   omega
 have hUnmatched:¬M.Adj (Z.vertex (2*j)) (Z.vertex (2*j+1)):= by
   intro hm
   have hodd:=(Z.MG (2*j) (by omega)).mp hm
   obtain ⟨k,hk⟩:= hodd
   omega
 let R: y7 S (Z.vertex (2*j)) (Z.vertex (2*j+1)):=
   { root:= r
     state:= A
     present:= hA
     J5:= P
     Lq:= hactive
     NX:= Q
     DL:= hPQ
     inside:= hQinside
     labelled:= hQlabel
     NC:= rfl
     MK:= hheld
     H9:= hextended
     bound:= by change j+1≤ ell;omega
     NW:= Z.vertex (2*j+2)
     matched:= Z.HR j hj.1
     Kq:= hfresh (2*j+1) (by omega) (by omega)
     Kp:= hfresh (2*j+2) (by omega) (by omega)
     My:= hj.2
     IY:= hlive j hj.1
     zV:= hUnmatched}
 exact ⟨j,hj.1,R,rfl,rfl⟩
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M H: SimpleGraph (Fin N)}
namespace C9
variable (S: C9 G M)
def take (n: ℕ) (hn: 0< n) (hnS: n≤ S.length): C9 G M where
 length:= n
 positive:= hn
 vertex:= S.vertex
 injective:= by intro i j hi hj he;exact S.injective i j (by omega) (by omega) he
 Mu:= by intro i hi;exact S.Mu i (by omega)
 MG:= by intro i hi;exact S.MG i (by omega)
lemma v7 (v: Fin N) (hv: v∈ S.support):
   ∃i,i< S.length∧ v∈ s(S.vertex (2*i),S.vertex (2*i+1)):= by
 obtain ⟨j,hj,rfl⟩:= mem_image.mp hv
 have hj':= mem_range.mp hj
 let i:= j/2
 have hi: i< S.length:= by dsimp [i];omega
 have he: j= 2*i∨ j= 2*i+1:= by dsimp [i];omega
 refine ⟨i,hi,Sym2.mem_iff.mpr ?_⟩
 exact he.elim (fun h=> Or.inl (congrArg S.vertex h)) (fun h=> Or.inr (congrArg S.vertex h))
lemma Iq: S.reverse.KA (S.length-1)=(S.KA 0).swap:= by
 have hp:= S.positive
 apply Prod.ext
 · change S.vertex (2*S.length-1-2*(S.length-1))= S.vertex (2*0+1)
   congr 1
   omega
 · change S.vertex (2*S.length-1-(2*(S.length-1)+1))= S.vertex (2*0)
   congr 1
   omega
end C9
namespace v9
variable {root: Fin N} (P: v9 G M root) (S: C9 G M)
lemma aQ (hM: Matching H M)
   (hedges:∀i,i< P.length→∀j,j< S.length→
     s(P.vertex (2*i+1),P.vertex (2*i+2))≠ s(S.vertex (2*j),S.vertex (2*j+1))):
   Disjoint P.support S.support:= by
 apply disjoint_left.mpr
 intro v hvP hvS
 obtain ⟨j,hj,hvj⟩:= S.v7 v hvS
 have hvr: v≠ root:= by
   intro he
   rw [he] at hvj
   have hm:= S.HR j hj
   rcases Sym2.mem_iff.mp hvj with hvj|hvj
   · exact P.L9 _ (hvj.symm ▸hm)
   · exact P.L9 _ (hvj.symm ▸hm.symm)
 obtain ⟨i,hi,hvi⟩:= P.v7 v hvP hvr
 exact hedges i hi j hj (m9 hM _ _
   (M.mem_edgeSet.mpr (P.HR i hi)) (M.mem_edgeSet.mpr (S.HR j hj)) v hvi hvj)
lemma tN (hd: Disjoint P.support S.support)
   (hG: G.Adj (P.vertex (2*P.length)) (S.vertex 0))
   (hM:¬M.Adj (P.vertex (2*P.length)) (S.vertex 0)):
   (P.Fr S hd hG hM).KA ((P.Fr S hd hG hM).length-1)= S.KA (S.length-1):= by
 have hp:= S.positive
 have hidx:(P.Fr S hd hG hM).length-1= P.length+(S.length-1):= by
   change P.length+S.length-1= P.length+(S.length-1)
   omega
 rw [hidx]
 exact P.wH S hd hG hM _
end v9
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
namespace C9
variable (C: C9 G M)
def Nq (H: SimpleGraph (Fin N)) (h:∀i,i< 2*C.length-1→ H.Adj (C.vertex i) (C.vertex (i+1))): C9 H M where
 length:= C.length
 positive:= C.positive
 vertex:= C.vertex
 injective:= C.injective
 Mu:= h
 MG:= C.MG
def LB (hC: 1< C.length): C9 G M where
 length:= C.length-1
 positive:= by omega
 vertex i:= C.vertex (i+2)
 injective:= by
   intro i j hi hj he
   have h:= C.injective (i+2) (j+2) (by omega) (by omega) he
   omega
 Mu:= by
   intro i hi
   have hh:= C.Mu (i+2) (by omega)
   convert hh using 1<;> congr 1<;> omega
 MG:= by
   intro i hi
   have hh:= C.MG (i+2) (by omega)
   have hp: Even (i+2)↔ Even i:= by rw [Nat.even_iff,Nat.even_iff];omega
   convert hh.trans hp using 1<;> congr 1<;> omega
lemma FH (hC: 1< C.length) (i: ℕ):(C.LB hC).KA i= C.KA (i+1):= by
 apply Prod.ext<;> change C.vertex _= C.vertex _<;> congr 1<;> omega
lemma DA (hC: 1< C.length):
   (C.LB hC).KA ((C.LB hC).length-1)= C.KA (C.length-1):= by
 rw [C.FH]
 change C.KA (C.length-1-1+1)= C.KA (C.length-1)
 congr 1
 omega
lemma wW (hC: 1< C.length):(C.LB hC).support ⊆C.support:= by
 intro v hv
 obtain ⟨i,hi,rfl⟩:= mem_image.mp hv
 exact C.mem_support (i+2) (by have h:=mem_range.mp hi;change i<2*(C.length-1) at h;omega)
end C9
namespace v9
variable {r: Fin N} (P: v9 G M r) (Q: C9 G M)
lemma l5 (hd: Disjoint P.support Q.support)
   (hG: G.Adj (P.vertex (2*P.length)) (Q.vertex 0)) (hM:¬M.Adj (P.vertex (2*P.length)) (Q.vertex 0)):
   (P.Fr Q hd hG hM).support ⊆P.support ∪Q.support:= by
 intro v hv
 obtain ⟨i,hi,rfl⟩:= mem_image.mp hv
 have hi': i≤ 2*(P.length+Q.length):= by have h:=mem_range.mp hi;change i<2*(P.length+Q.length)+1 at h;omega
 change P.GF Q i∈ P.support ∪Q.support
 by_cases h: i≤ 2*P.length
 · rw [GF,if_pos h]
   exact mem_union_left _ (P.mem_support i h)
 · rw [GF,if_neg h]
   exact mem_union_right _ (Q.mem_support _ (P.vW Q i (by omega) hi'))
end v9
end Be
end
noncomputable section
namespace Be.G8
variable {N: ℕ} {G M: SimpleGraph (Fin N)} (F: G8 G M)
lemma e5 (hM: Matching G M) (C: C9 G M)
   (hlinks:∀i,i+1< C.length→ F.JV (C.KA i) (C.KA (i+1)).swap)
   {r: Fin N} (A: Lp G M r) (hA: F.state r= some A)
   (hfirst:(C.KA 0).1∈ A.tree.vertices): C.support ⊆A.tree.vertices:= by
 have hEnds (i: ℕ) (hi: i< C.length):(C.KA i).1∈ A.tree.vertices∧(C.KA i).2∈ A.tree.vertices:= by
   have hContains:= F.gF C.KA C.length hlinks r ⟨A,hA,hfirst⟩ i hi
   obtain ⟨B,hB,hiB⟩:= hContains
   have hBA: B= A:= Option.some.inj (hB.symm.trans hA)
   subst B
   exact ⟨hiB,A.tree.iA hM _ hiB _ (C.HR i hi)⟩
 intro v hv
 obtain ⟨i,hi,hvi⟩:= C.v7 v hv
 have h:= hEnds i hi
 rcases Sym2.mem_iff.mp hvi with hv|hv
 · exact hv.symm ▸h.1
 · exact hv.symm ▸h.2
end Be.G8
end
noncomputable section
namespace Be.v9
variable {N: ℕ} {G H M: SimpleGraph (Fin N)} {r: Fin N}
   (P: v9 G M r) (Q: C9 G M)
lemma bL (hM: Matching H M) (E: Finset (Fin N ×Fin N)) (i: ℕ)
   (hleaf: i+1= P.length) (havoid: P.E8 E i)
   (hE:∀j,j< Q.length→ Q.KA j∈ E∧(Q.KA j).swap∈ E):
   Disjoint P.support Q.support:= by
 apply P.aQ Q hM
 intro a ha b hb heq
 have hab: a≤ i:= by omega
 have hnot:= havoid a hab
 rcases Sym2.eq_iff.mp heq with heq|heq
 · have he: P.KA a= Q.KA b:= Prod.ext heq.1 heq.2
   rw [he] at hnot
   exact hnot (hE b hb).1
 · have he: P.KA a=(Q.KA b).swap:= Prod.ext heq.1 heq.2
   rw [he] at hnot
   exact hnot (hE b hb).2
end Be.v9
end
noncomputable section
namespace Be
variable {N: ℕ} {G M H: SimpleGraph (Fin N)} {root: Fin N}
namespace C9
variable (S: C9 G M)
lemma yL (hM: Matching H M) (i: ℕ) (hi0: 0< i) (hi: i< S.length)
   (hNo:¬Fk G M root (S.KA 0).swap)
   (hprev:∀j,j< i→ G2 G M root (S.KA 0) (S.KA j)∧
     G2 G M root (S.KA 0) (S.KA j).swap):
   G2 G M root (S.KA 0) (S.KA i).swap:= by
 intro P hPl hlast hPA
 let T:= S.take i hi0 hi.le
 have hedges:∀k,k< P.length→∀j,j< i→
     s(P.vertex (2*k+1),P.vertex (2*k+2))≠ s(S.vertex (2*j),S.vertex (2*j+1)):= by
   intro k hk j hj heq
   let Q:= P.take (k+1) (by omega)
   have hQl: 0< Q.length:= by change 0< k+1;omega
   have hQA: Q.Nt {S.KA 0}:= P.JI _ hPA _ _
   have hQlast: Q.KA (Q.length-1)= P.KA k:= by
     change P.KA (k+1-1)= P.KA k
     rw [Nat.add_sub_cancel]
   rcases Sym2.eq_iff.mp heq with hs|hr
   · have he: P.KA k= S.KA j:= Prod.ext hs.1 hs.2
     exact (hprev j hj).1 Q hQl (hQlast.trans he) hQA
   · have he: P.KA k=(S.KA j).swap:= Prod.ext hr.1 hr.2
     exact (hprev j hj).2 Q hQl (hQlast.trans he) hQA
 have hdis: Disjoint P.support T.reverse.support:= by
   rw [T.CF]
   apply P.aQ T hM
   exact hedges
 have hhead: P.vertex (2*P.length)= S.vertex (2*i):= by
   have hh: P.vertex (2*(P.length-1)+2)= S.vertex (2*i):= congrArg Prod.snd hlast
   rwa [show 2*(P.length-1)+2= 2*P.length by omega] at hh
 have hfirst: T.reverse.vertex 0= S.vertex (2*i-1):= by
   change S.vertex (2*i-1-0)= S.vertex (2*i-1)
   rw [Nat.sub_zero]
 have hbridge: G.Adj (P.vertex (2*P.length)) (T.reverse.vertex 0):= by
   rw [hhead,hfirst]
   have hh:= S.Mu (2*i-1) (by omega)
   rw [show 2*i-1+1= 2*i by omega] at hh
   exact hh.symm
 have hunmatched:¬M.Adj (P.vertex (2*P.length)) (T.reverse.vertex 0):= by
   rw [hhead,hfirst]
   intro hm
   have hh:= S.MG (2*i-1) (by omega)
   rw [show 2*i-1+1= 2*i by omega] at hh
   obtain ⟨j,hj⟩:= hh.mp hm.symm
   omega
 let R:= P.Fr T.reverse hdis hbridge hunmatched
 have hRl: 0< R.length:= by change 0< P.length+i;omega
 have hRlast: R.KA (R.length-1)=(S.KA 0).swap:=
   (P.tN T.reverse hdis hbridge hunmatched).trans T.Iq
 exact hNo ⟨R,hRl,hRlast⟩
lemma Bu (hM: Matching H M)
   (hNo:¬Fk G M root (S.KA 0).swap)
   (hreach:∀i,0< i→ i< S.length→ Fk G M root (S.KA i).swap):
   ∀i,i< S.length→ G2 G M root (S.KA 0) (S.KA i)∧
     G2 G M root (S.KA 0) (S.KA i).swap:= by
 intro i
 induction i using Nat.strong_induction_on with
 | h i ih =>
   intro hi
   by_cases hi0: i= 0
   · subst i
     refine ⟨Dz _,?_⟩
     intro P hPl hlast hPA
     exact hNo ⟨P,hPl,hlast⟩
   · have hipos: 0< i:= by omega
     have hrev:= S.yL hM i hipos hi hNo (fun j hj=> ih j hj (hj.trans hi))
     have hfwd:= wV hM (S.KA 0) (S.KA i).swap hNo (hreach i hipos hi) hrev
     exact ⟨by simpa only [Prod.swap_swap] using hfwd,hrev⟩
end C9
end Be
end
noncomputable section
namespace Be.C9
variable {N: ℕ} {G H M: SimpleGraph (Fin N)} (C: C9 G M)
def z5: Finset (Fin N ×Fin N):=
 (Ico 1 C.length).biUnion (fun i=>{C.KA i,(C.KA i).swap})
lemma e4 (i: ℕ) (hi0: 0< i) (hi: i< C.length):
   C.KA i∈ C.z5∧(C.KA i).swap∈ C.z5:= by
 constructor
 · exact mem_biUnion.mpr ⟨i,mem_Ico.mpr ⟨by omega,hi⟩,mem_insert_self _ _⟩
 · exact mem_biUnion.mpr ⟨i,mem_Ico.mpr ⟨by omega,hi⟩,mem_insert_of_mem (mem_singleton_self _)⟩
lemma kG (e: Fin N ×Fin N) (he: e∈ C.z5):
   ∃i,0< i∧ i< C.length∧(e= C.KA i∨ e=(C.KA i).swap):= by
 obtain ⟨i,hi,he⟩:= mem_biUnion.mp he
 exact ⟨i,by have h:=(mem_Ico.mp hi).1;omega,(mem_Ico.mp hi).2,by simpa only [mem_insert,mem_singleton] using he⟩
lemma dX: C.KA 0∉ C.z5:= by
 intro he
 obtain ⟨i,hi0,hi,he|he⟩:= C.kG _ he
 · have hh:= congrArg Prod.fst he
   change C.vertex 0= C.vertex (2*i) at hh
   have hpos:= C.positive
   have hidx:= C.injective 0 (2*i) (by omega) (by omega) hh
   omega
 · have hh:= congrArg Prod.fst he
   change C.vertex 0= C.vertex (2*i+1) at hh
   have hpos:= C.positive
   have hidx:= C.injective 0 (2*i+1) (by omega) (by omega) hh
   omega
lemma eR {r: Fin N} (hM: Matching H M)
   (hNo:¬Fk G M r (C.KA 0).swap)
   (hReverse:∀j,0< j→ j< C.length→ Fk G M r (C.KA j).swap)
   (P: v9 G M r) (i: ℕ) (hi: i< P.length) (hFirst: P.KA i= C.KA 0):
   P.E8 C.z5 i:= by
 intro j hj hFuture
 have hjlt: j< i:= by
   by_contra hn
   have heq: j= i:= by omega
   rw [heq,hFirst] at hFuture
   exact C.dX hFuture
 obtain ⟨x,hx0,hx,hOrient⟩:= C.kG _ hFuture
 let Q:= P.take (j+1) (by omega)
 have hQpos: 0< Q.length:= by change 0<j+1;omega
 have hQlast: Q.KA (Q.length-1)= P.KA j:= by
   change P.KA (j+1-1)=P.KA j
   rw [Nat.add_sub_cancel]
 have hAvoid: Q.Nt {C.KA 0}:= by
   intro a ha hmem
   have ha': a< j+1:= ha
   have he: P.KA a= P.KA i:=(mem_singleton.mp hmem).trans hFirst.symm
   have hidx:= P.pB a i (by omega) hi he
   omega
 have hDom:= C.Bu hM hNo hReverse x hx
 rcases hOrient with he|he
 · exact hDom.1 Q hQpos (hQlast.trans he) hAvoid
 · exact hDom.2 Q hQpos (hQlast.trans he) hAvoid
end Be.C9
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma C9.s4 (C: C9 G M) (i: ℕ) (hi: i+1< C.length):
   ¬M.Adj (C.KA i).2 (C.KA (i+1)).1:= by
 intro hm
 have hm': M.Adj (C.vertex (2*i+1)) (C.vertex (2*i+2)):= by convert hm using 1<;> congr 1<;> omega
 have hp:=(C.MG (2*i+1) (by omega)).mp hm'
 obtain ⟨j,hj⟩:= hp
 omega
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma Lp.EZ {r: Fin N} (A: Lp G M r) (e: Fin N ×Fin N) (k: ℕ)
   (E: Finset (Fin N ×Fin N)) (h: A.Ny e k E): M.Adj e.1 e.2:= by
 obtain ⟨P,i,hP,hi,hik,hie,havoid⟩:= h
 have hm:= P.HR i hi
 change M.Adj (P.KA i).1 (P.KA i).2 at hm
 rwa [hie] at hm
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma Lp.y0 {r: Fin N} (A: Lp G M r) (e: Fin N ×Fin N)
   {k l: ℕ} (hkl: k≤ l) (E: Finset (Fin N ×Fin N)) (h: A.Ny e k E): A.Ny e l E:= by
 obtain ⟨P,i,hP,hi,hik,hie,havoid⟩:= h
 exact ⟨P,i,hP,hi,hik.trans hkl,hie,havoid⟩
namespace G8
def Lh (F: G8 G M) (e: Fin N ×Fin N): Prop:=∃k,F.Ny e k ∅
end G8
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma G8.tK (F: G8 G M) {r: Fin N} (A: Lp G M r)
   (hA: F.state r= some A) (P: v9 G M r) (hP: A.active= some P)
   (i: ℕ) (hi: i< P.length) (e: Fin N ×Fin N) (he: P.KA i= e): F.Lh e:= by
 refine ⟨i,r,A,hA,P,i,hP,hi,le_rfl,he,?_⟩
 intro j hj hmem;simp at hmem
lemma cE (S: tI G M ell)
   (hInternal: S.zA) (C: C9 G M)
   (hLinks:∀j,j+1< C.length→ S.ND.JV (C.KA j) (C.KA (j+1)).swap)
   (hForward: S.ND.M7 (C.KA 0))
   (hReverse:∀j,0< j→ j< C.length→ S.ND.M7 (C.KA j).swap)
   (hLive:∀j,j< 2*C.length-1→ S.NV.Adj (C.vertex j) (C.vertex (j+1)))
   (hInactive:¬S.ND.Lh (C.KA 0))
   {r: Fin N} (A: Lp G M r) (hA: S.ND.state r= some A)
   (P: v9 G M r) (hactive: A.active= some P) (i: ℕ) (hi: i< P.length)
   (x: ℕ) (hx0: 0< x) (hx: x< C.length)
   (hEnd: P.KA i= C.KA x∨ P.KA i=(C.KA x).swap):
   S.ND.IP (C.KA 0):= by
 have hPi:= A.tL P hactive i hi
 have hEnds:= A.tree.yG _ hPi
 have hTarget:(C.KA x).1∈ A.tree.vertices:= by
   rcases hEnd with he|he
   · rw [he] at hEnds;exact hEnds.1
   · rw [he] at hEnds;exact hEnds.2
 obtain ⟨s,B,hB,hFirst⟩:= hForward
 have hSupportB:= S.ND.e5 S.MG C hLinks B hB (B.tree.yG _ hFirst).1
 have hsr:= S.ND.BE s r (C.KA x).1
   ⟨B,hB,hSupportB (C.mem_support (2*x) (by omega))⟩ ⟨A,hA,hTarget⟩
 subst s
 have hBA: B= A:= Option.some.inj (hB.symm.trans hA)
 subst B
 by_contra hNotSettled
 have hNoReverse:¬A.tree.Reaches (C.KA 0).swap:= fun h=> hNotSettled ⟨r,A,hA,hFirst,h⟩
 let D:= C.Nq (Mv G A.tree.NS) (fun j hj=>
   S.o3 hInternal A hA _ _ (hLive j hj)
     (hSupportB (C.mem_support j (by omega))) (hSupportB (C.mem_support (j+1) (by omega))))
 have hReverseA:∀j,0< j→ j< D.length→ Fk (Mv G A.tree.NS) M r (D.KA j).swap:= by
   intro j hj0 hj
   exact S.ND.AJ (C.KA j).swap A hA
     (hSupportB (C.mem_support (2*j+1) (by change j<C.length at hj;omega))) (hReverse j hj0 hj)
 let Q:=(P.take (i+1) (by omega)).Kt A.tree.NS (P.JJ A.tree.NS (A.inside P hactive) (i+1) (by omega))
 have hQpos: 0< Q.length:= by change 0< i+1;omega
 have hQlast: Q.KA (Q.length-1)= P.KA i:= by
   change P.KA (i+1-1)=P.KA i
   rw [Nat.add_sub_cancel]
 have hAvoid: Q.Nt {C.KA 0}:= by
   intro j hj hmem
   have hj': j< i+1:= hj
   have he: P.KA j= C.KA 0:= mem_singleton.mp hmem
   exact hInactive (S.ND.tK A hA P hactive j (by omega) _ he)
 have hDom:= D.Bu S.MG hNoReverse hReverseA x hx
 rcases hEnd with he|he
 · exact hDom.1 Q hQpos (hQlast.trans he) hAvoid
 · exact hDom.2 Q hQpos (hQlast.trans he) hAvoid
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
namespace G8
def M5 (F: G8 G M) (lab: Fin N ×Fin N→ ℕ): Prop:=
 ∀r R,F.state r= some R→ R.M5 lab
end G8
lemma Lp.E0 {r: Fin N} (A: Lp G M r) (e: Fin N ×Fin N) (k: ℕ)
   (E: Finset (Fin N ×Fin N)) (h: A.Ny e k E): A.tree.Reaches e:= by
 obtain ⟨P,i,hP,hi,hik,hie,havoid⟩:= h
 have hr:= A.tL P hP i hi
 rwa [hie] at hr
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma Bi.vM {r: Fin N} (A B: Bi G M r)
   (hGraph: Mv G A.NS≤ Mv G B.NS) (e: Fin N ×Fin N) (h: A.Reaches e): B.Reaches e:= by
 obtain ⟨P,hp,he⟩:= h
 exact ⟨P.NM hGraph,hp,he⟩
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma tI.oL (S: tI G M ell)
   (hInternal: S.zA) (hNo: S.ND.n8 S.NV)
   (a: ℕ→ Fin N ×Fin N) (n: ℕ)
   (hforward:∀i,i+1< n→∃r,S.ND.Reaches r (a i))
   (hreverse:∀i,i+1< n→∃r,S.ND.Reaches r (a (i+1)).swap)
   (hconnect:∀i,i+1< n→ S.NV.Adj (a i).2 (a (i+1)).1)
   (hUnmatched:∀i,i+1< n→¬M.Adj (a i).2 (a (i+1)).1):
   ∀i,i+1< n→ S.ND.JV (a i) (a (i+1)).swap:= by
 intro i hi
 exact S.mT hInternal hNo (a i) (a (i+1)).swap (hforward i hi) (hreverse i hi) (hconnect i hi) (hUnmatched i hi)
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma tI.oM (S: tI G M ell)
   (hInternal: S.zA) (hNo: S.ND.n8 S.NV)
   (C: C9 G M)
   (hForward: S.ND.M7 (C.KA 0))
   (hSettled:∀j,0< j→ j+1< C.length→ S.ND.IP (C.KA j))
   (hTarget: S.ND.M7 (C.KA (C.length-1)).swap)
   (hLive:∀j,j< 2*C.length-1→ S.NV.Adj (C.vertex j) (C.vertex (j+1))):
   (∀j,j+1< C.length→ S.ND.JV (C.KA j) (C.KA (j+1)).swap)∧
   (∀j,0< j→ j< C.length→ S.ND.M7 (C.KA j).swap):= by
 have hReverse:∀j,0< j→ j< C.length→ S.ND.M7 (C.KA j).swap:= by
   intro j hj0 hj
   by_cases heq: j= C.length-1
   · rw [heq];exact hTarget
   · obtain ⟨r,R,hR,hf,hr⟩:= hSettled j hj0 (by omega)
     exact ⟨r,R,hR,hr⟩
 have hForwardAll:∀j,j+1< C.length→ S.ND.M7 (C.KA j):= by
   intro j hj
   by_cases hj0: j= 0
   · rw [hj0];exact hForward
   · obtain ⟨r,R,hR,hf,hr⟩:= hSettled j (by omega) hj
     exact ⟨r,R,hR,hf⟩
 have hConnect:∀j,j+1< C.length→ S.NV.Adj (C.KA j).2 (C.KA (j+1)).1:= by
   intro j hj
   have h:= hLive (2*j+1) (by omega)
   convert h using 1<;> congr 1<;> omega
 exact ⟨S.oL hInternal hNo C.KA C.length hForwardAll
   (fun j hj=> hReverse (j+1) (by omega) hj) hConnect (fun j hj=> C.s4 j hj),hReverse⟩
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
def tC (F: G8 G M) (C: C9 G M): Prop:=
 ∃(r: Fin N) (A: Lp G M r) (P: v9 G M r) (i x: ℕ),
   F.state r= some A∧ A.active= some P∧ i< P.length∧ x< C.length∧
   (P.KA i= C.KA x∨ P.KA i=(C.KA x).swap)
def wC (states: ℕ→ tI G M ell) (C: C9 G M) (T: ℕ): Prop:=
 ∃t,0< t∧ t< T∧
   (∀j,j+1< C.length→(states t).ND.IP (C.KA j))∧
   (states t).ND.M7 (C.KA (C.length-1)).swap∧
   tC (states t).ND C
lemma C9.D8 (C: C9 G M) (S: tI G M ell)
   (hLive:∀j,j< 2*C.length-1→ S.NV.Adj (C.vertex j) (C.vertex (j+1)))
   (j: ℕ) (hj: j< C.length):
   (C.KA j).1∉ S.Nm∧(C.KA j).2∉ S.Nm:=
 S.HK _ _ (hLive (2*j) (by omega))
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {r: Fin N}
namespace v9
variable (P: v9 G M r)
def F8 (k: ℕ) (hk: k< P.length): C9 G M where
 length:= P.length-k
 positive:= by omega
 vertex i:= P.vertex (2*k+1+i)
 injective:= by
   intro i j hi hj he
   have hh:= P.injective (2*k+1+i) (2*k+1+j) (by omega) (by omega) he
   omega
 Mu:= by
   intro i hi
   have hh:= P.Mu (2*k+1+i) (by omega)
   convert hh using 1<;> congr 1<;> omega
 MG:= by
   intro i hi
   have hh:= P.MG (2*k+1+i) (by omega)
   have hp: Odd (2*k+1+i)↔ Even i:= by
     rw [Nat.odd_iff,Nat.even_iff]
     omega
   change M.Adj (P.vertex (2*k+1+i)) (P.vertex (2*k+1+(i+1)))↔ Even i
   simpa only [Nat.add_assoc] using hh.trans hp
lemma xI (k: ℕ) (hk: k< P.length) (i: ℕ):
   (P.F8 k hk).KA i= P.KA (k+i):= by
 apply Prod.ext<;> change P.vertex _= P.vertex _<;> congr 1<;> omega
lemma uP (k: ℕ) (hk: k< P.length):
   (P.F8 k hk).KA ((P.F8 k hk).length-1)= P.KA (P.length-1):= by
 rw [P.xI]
 congr 1
 change k+(P.length-k-1)=P.length-1
 omega
lemma uQ (k: ℕ) (hk: k< P.length) (H: SimpleGraph (Fin N))
   (hLive:∀j,j< 2*P.length→ H.Adj (P.vertex j) (P.vertex (j+1))):
   ∀j,j< 2*(P.F8 k hk).length-1→
     H.Adj ((P.F8 k hk).vertex j) ((P.F8 k hk).vertex (j+1)):= by
 intro j hj
 have hh:= hLive (2*k+1+j) (by change j<2*(P.length-k)-1 at hj;omega)
 change H.Adj (P.vertex (2*k+1+j)) (P.vertex (2*k+1+(j+1)))
 simpa only [Nat.add_assoc] using hh
end v9
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell} {x y: Fin N}
lemma y7.BS (R: y7 S x y) (i: ℕ)
   (hi: i< R.NX.length) (hAfter: R.J5.length≤ i):
   ¬S.ND.Lh (R.NX.KA i):= by
 rintro ⟨k,r,A,hA,P,j,hP,hj,hjk,hje,havoid⟩
 have hmem:(R.NX.KA i).1∈ R.state.tree.vertices:=
   R.state.tree.EA R.NX R.inside (R.NX.mem_support (2*i+1) (by omega))
 have hAmem:= A.tree.EA P (A.inside P hP) (P.mem_support (2*j+1) (by omega))
 change (P.KA j).1∈ A.tree.vertices at hAmem
 rw [hje] at hAmem
 have heq:= S.ND.BE r R.root (R.NX.KA i).1 ⟨A,hA,hAmem⟩ ⟨R.state,R.present,hmem⟩
 subst r
 have hAR: A=R.state:= Option.some.inj (hA.symm.trans R.present)
 subst A
 have hPP: P=R.J5:= Option.some.inj (hP.symm.trans R.Lq)
 subst P
 have hExt:= R.J5.I4 R.DL j hj
 have hEqual: R.NX.KA j= R.NX.KA i:= hExt.trans hje
 have hij:= R.NX.pB j i (hj.trans_le R.DL.1) hi hEqual
 omega
lemma M2.w9 {mode: Bool} {es: List (Fin N ×Fin N)} (h: M2 mode es S T)
   (e: Fin N ×Fin N) (halive: e.1∉ T.Nm) (hInactive:¬T.ND.Lh e):
   T.labels e= S.labels e:= by
 have hm:= h.Jj e
 by_contra hn
 obtain ⟨r,A,hA,hm,hTrack⟩:= h.o6 e halive (by omega)
 exact hInactive ⟨T.labels e-1,r,A,hA,hTrack⟩
lemma M2.w8 {mode: Bool} {es: List (Fin N ×Fin N)} (h: M2 mode es S T)
   (e: Fin N ×Fin N) (halive: e.1∉ T.Nm) (hInactive:¬T.ND.Lh e):
   ¬S.ND.Lh e:= by
 rintro ⟨k,hs⟩
 exact hInactive ⟨k,h.DE e k halive hs⟩
lemma tI.G9 (S: tI G M ell) (limit: ℕ)
   (e: Fin N ×Fin N) (h: S.ND.Lh e):(S.IX limit).ND.Lh e:= by
 obtain ⟨k,r,A,hA,P,i,hP,hi,hik,hie,havoid⟩:= h
 refine ⟨k,r,A.IX limit,?_,P,i,hP,hi,hik,hie,havoid⟩
 change (S.ND.state r).map (fun R=> R.IX limit)= some (A.IX limit)
 rw [hA]
 rfl
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S: tI G M ell} {x y: Fin N}
namespace y7
variable (R: y7 S x y)
def targetPath: v9 G M R.root:=
 R.NX.Fq y R.NW (S.MF R.Do) (S.MG.1 R.matched)
   R.y1 R.matched R.Kq R.Kp
lemma CR:∀j,j< 2*R.targetPath.length→
   S.NV.Adj (R.targetPath.vertex j) (R.targetPath.vertex (j+1)):= by
 have hs:∀j,j< 2*R.NX.length→ S.NV.Adj (R.NX.vertex j) (R.NX.vertex (j+1)):=
   fun j hj=> S.I9 R.root R.state R.present _ _ (R.inside j hj)
 let P:= R.NX.Nq S.NV hs
 have hLiveM:= S.HQ y R.NW R.matched (S.HK _ _ R.IY).2
 let Q:= P.Fq y R.NW R.Do hLiveM R.y1 R.matched R.Kq R.Kp
 exact Q.Mu
lemma p8 (i: ℕ) (hi: i< R.NX.length):
   R.targetPath.KA i= R.NX.KA i:=
 R.NX.I4 (R.NX.l3 y R.NW (S.MF R.Do)
   (S.MG.1 R.matched) R.y1 R.matched R.Kq R.Kp) i hi
lemma v0: R.targetPath.KA (R.targetPath.length-1)=(y,R.NW):= by
 change R.targetPath.KA (R.NX.length+1-1)=(y,R.NW)
 rw [Nat.add_sub_cancel]
 exact R.NX.tM y R.NW (S.MF R.Do)
   (S.MG.1 R.matched) R.y1 R.matched R.Kq R.Kp
end y7
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S: tI G M ell} {x y: Fin N} {R: y7 S x y}
lemma Bb.i4 (A: Bb R)
   {r: Fin N} (B: Lp G M r) (hB: A.Nj.ND.state r= some B)
   (hne: r≠ R.root) (e: Fin N ×Fin N) (he: e.1∈ B.tree.vertices):
   A.Nj.labels e= S.labels e:= by
 rw [A.LO]
 apply A.Nf.EH S.labels e
 intro i hi hie
 obtain ⟨C,hC,hP,hm,hExt,hHeld⟩:= A.EG
 have hmem:= C.tree.EA A.Nf (C.inside A.Nf hP) (A.Nf.mem_support (2*i+1) (by omega))
 change (A.Nf.KA i).1∈ C.tree.vertices at hmem
 rw [hie] at hmem
 exact disjoint_left.mp (A.Nj.ND.disjoint R.root r hne.symm C B hC hB) hmem he
lemma Bb.jC (A: Bb R)
   {r: Fin N} (Q: Lp G M r) (hQ: A.Nj.ND.state r= some Q)
   (hne: r≠ R.root) (P: v9 G M r) (hP: Q.active= some P):
   ∃(B: Lp G M r) (old: v9 G M r),
     S.ND.state r= some B∧ B.active= some old∧ P.M4 old:= by
 cases A with
 | single hOwner =>
   change Function.update S.ND.state R.root _ r= some Q at hQ
   rw [Function.update_of_ne hne] at hQ
   exact ⟨Q,P,hQ,hP,le_rfl,fun _ _=> rfl⟩
 | @inactive beta D B hB hAT hBT hStem hTarget hInactive =>
   by_cases hrb: r=beta
   · subst r
     change S.ND.E2 _ _ beta= some Q at hQ
     rw [G8.E3] at hQ
     cases Option.some.inj hQ
     exact ⟨B,P,hB,hP,le_rfl,fun _ _=> rfl⟩
   · change S.ND.E2 _ _ r= some Q at hQ
     rw [G8.C0 _ _ _ _ hne hrb] at hQ
     exact ⟨Q,P,hQ,hP,le_rfl,fun _ _=> rfl⟩
 | @active beta D B hB hAT hBT hStem hTarget hActive =>
   by_cases hrb: r=beta
   · subst r
     change S.ND.E2 _ _ beta= some Q at hQ
     rw [G8.E3] at hQ
     cases Option.some.inj hQ
     change some (D.Ng.take (D.index-1) _)= some P at hP
     cases Option.some.inj hP
     exact ⟨B,D.Ng,hB,hActive,D.Ng.ID _ _⟩
   · change S.ND.E2 _ _ r= some Q at hQ
     rw [G8.C0 _ _ _ _ hne hrb] at hQ
     exact ⟨Q,P,hQ,hP,le_rfl,fun _ _=> rfl⟩
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S: tI G M ell} {x y: Fin N} {R: y7 S x y}
lemma Bb.jB (A: Bb R)
   (hNow: S.ND.M5 S.labels) (hStem: IN R.state.tree R.NX S.labels)
   (i: ℕ) (hi: i< A.Nf.length)
   (hShort: A.Nj.labels (A.Nf.KA i)< i+1):
   A.Nj.ND.M7 (A.Nf.KA i).swap:= by
 have hOld:=(A.Nf.yH S.labels i hi (by rwa [←A.LO])).2
 have hTransfer:∀(r: Fin N) (B: Lp G M r),S.ND.state r= some B→
     ∀e,B.tree.Reaches e→ A.Nj.ND.M7 e:= by
   intro r B hB e he
   exact A.yF e ⟨r,B,hB,he⟩
 by_cases hiStem: i< R.NX.length
 · have he:= R.NX.I4 A.Iz i hiStem
   rw [he] at hOld ⊢
   exact hTransfer R.root R.state R.present _ (hStem i hiStem hOld)
 · cases A with
   | single hOwner =>
     have hiEq: i=R.NX.length:= by change i<R.NX.length+1 at hi;omega
     subst i
     have he:= R.NX.tM y R.NW (S.MF R.Do)
       (S.MG.1 R.matched) R.y1 R.matched R.Kq R.Kp
     change S.labels (R.targetPath.KA R.NX.length)<R.NX.length+1 at hOld
     change R.targetPath.KA R.NX.length=(y,R.NW) at he
     rw [he] at hOld
     have hE:=R.My
     omega
   | inactive D B hB hAT hBT hSt hTarget hInactive =>
     have hiEq: i=D.NX.length:= by rw [hSt];change i<D.NX.length+1 at hi;rw [hSt] at hi;omega
     subst i
     change S.labels (D.K6.KA D.NX.length)<D.NX.length+1 at hOld
     rw [D.yT,hSt,hTarget] at hOld
     have hE:=R.My
     omega
   | @active beta D B hB hAT hBT hSt hTarget hActive =>
     let j:= i-D.data.NX.length+D.index-1
     have hb:= D.bound
     have hp:= D.positive
     have hI: D.data.NX.length≤ i:= by rw [hSt];omega
     have hj: j<D.Ng.length:= by
       change i<D.data.NX.length+(D.Ng.length+1-D.index) at hi
       dsimp [j];omega
     have hLabel:=(S.labelled beta B hB D.Ng hActive).2 (D.index-1) (by omega)
     change S.labels (D.Ng.KA (D.index-1))≤ D.index-1+1 at hLabel
     rw [D.target,hTarget] at hLabel
     have hE: D.data.NX.length+1< S.labels (y,R.NW):= by rw [hSt];exact R.My
     have hij: i≤ j:= by dsimp [j];omega
     have he:= D.data.NX.fQ D.Ng D.index D.positive D.bound D.separation D.Nz D.zV i hI
     change D.path.KA i= D.Ng.KA j at he
     change S.labels (D.path.KA i)< i+1 at hOld
     change G8.M7 _ (D.path.KA i).swap
     rw [he] at hOld ⊢
     exact hTransfer beta B hB _ (hNow beta B hB D.Ng hActive j hj (by omega))
lemma Bb.Nb (A: Bb R)
   (hNow: S.ND.M5 S.labels) (hStem: IN R.state.tree R.NX S.labels):
   A.Nj.ND.M5 A.Nj.labels:= by
 intro r B hB P hP i hi hShort
 have hTail:= B.tree.EA P (B.inside P hP) (P.mem_support (2*i+1) (by omega))
 have hHead:= B.tree.EA P (B.inside P hP) (P.mem_support (2*i+2) (by omega))
 apply A.Nj.ND.AJ (P.KA i).swap B hB hHead
 by_cases hr: r=R.root
 · subst r
   obtain ⟨Q,hQ,hQP,hm,he,hh⟩:= A.EG
   have hBQ: B=Q:= Option.some.inj (hB.symm.trans hQ)
   subst B
   have hPath: P=A.Nf:= Option.some.inj (hP.symm.trans hQP)
   subst P
   exact A.jB hNow hStem i hi hShort
 · obtain ⟨oldB,oldP,hOldB,hOldP,hExt⟩:= A.jC B hB hr P hP
   have hFix:= A.i4 B hB hr (P.KA i) hTail
   rw [hFix] at hShort
   have he:= P.I4 hExt i hi
   rw [←he] at hShort
   have hReach:= hNow r oldB hOldB oldP hOldP i (hi.trans_le hExt.1) hShort
   rw [he] at hReach
   exact A.yF _ ⟨r,oldB,hOldB,hReach⟩
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma G8.Ji (F: G8 G M) (lab: Fin N ×Fin N→ ℕ)
   (f:∀r,Lp G M r→ Lp G M r)
   (hv:∀r R,(f r R).tree.vertices= R.tree.vertices)
   (hf:∀r R,R.M5 lab→(f r R).M5 lab) (h: F.M5 lab):
   (F.LU f hv).M5 lab:= by
 intro r R hR
 change (F.state r).map (f r)=some R at hR
 obtain ⟨A,hA,he⟩:= Option.map_eq_some_iff.mp hR
 rw [←he]
 exact hf r A (h r A hA)
lemma tI.F3 (S: tI G M ell) (limit: ℕ)
   (h: S.ND.M5 S.labels):(S.IX limit).ND.M5 (S.IX limit).labels:=
 S.ND.Ji _ (fun _ R=> R.IX limit) (fun _ _=> rfl) (fun _ _ h=> h) h
lemma tI.HF (S: tI G M ell) (limit: ℕ)
   (h: S.ND.M5 S.labels):(S.rC limit).ND.M5 (S.rC limit).labels:=
 S.ND.Ji _ (fun _ R=> R.rC limit) (fun _ _=> rfl) (fun _ _ h=> h) h
lemma tI.xB (S: tI G M ell)
   (h: S.ND.M5 S.labels): S.Dk.ND.M5 S.Dk.labels:= by
 apply S.ND.Ji _ _ (by intro r R;unfold Lp.zS;split_ifs<;> rfl) _ h
 intro r R hR
 unfold Lp.zS
 split_ifs
 · exact hR
 · exact R.wK S.labels hR
lemma tI.BT (S: tI G M ell)
   (h: S.ND.M5 S.labels): S.z9.ND.M5 S.z9.labels:= by
 apply S.ND.Ji _ _ (fun _ R=> R.fA S.NV S.MF) _ h
 intro r R hR P hP i hi hShort
 apply Bi.fJ
 exact hR P hP i hi hShort
lemma M3.Ad {mode: Bool} {x y: Fin N} (h: M3 mode x y S T)
   (hNow: S.ND.M5 S.labels)
   (hStem:∀R: y7 S x y,IN R.state.tree R.NX S.labels):
   T.ND.M5 T.labels:= by
 cases h with
 | augmentation R hflag =>
   intro r A hA
   change (if r∈({R.ME,R.L7}:Finset (Fin N)) then none else S.ND.state r)=some A at hA
   split_ifs at hA
   exact hNow r A hA
 | extension hmode R hNo A => exact A.Nb hNow (hStem R)
 | skip hNo hNoExt => exact hNow
lemma M3.F4 {x y: Fin N} (h: M3 false x y S T)
   (hNow: S.ND.M5 S.labels): T.ND.M5 T.labels:= by
 cases h with
 | augmentation R hflag =>
   intro r A hA
   change (if r∈({R.ME,R.L7}:Finset (Fin N)) then none else S.ND.state r)=some A at hA
   split_ifs at hA
   exact hNow r A hA
 | extension hmode => cases hmode
 | skip hNo hNoExt => exact hNow
lemma M2.F4 {es: List (Fin N ×Fin N)} (h: M2 false es S T)
   (hNow: S.ND.M5 S.labels): T.ND.M5 T.labels:= by
 induction h with
 | nil => exact hNow
 | cons step rest ih => exact ih (step.F4 hNow)
lemma M2.append {mode: Bool} {es fs: List (Fin N ×Fin N)}
   {U: tI G M ell} (h: M2 mode es S T) (k: M2 mode fs T U):
   M2 mode (es++fs) S U:= by
 induction h with
 | nil => exact k
 | cons step rest ih => exact M2.cons step (ih k)
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma tI.BQ (hM: Matching G M):
   (tI.initial G M hM ell).ND.M5 (tI.initial G M hM ell).labels:= by
 intro r A hA P hP i hi hShort
 have hL:=(tI.initial G M hM ell).labelled r A hA P hP
 change ell+1< i+1 at hShort
 have hLen:= hL.1
 omega
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell} {x y: Fin N}
lemma Bb.qO {R: y7 S x y} (A: Bb R)
   (r: Fin N) (hActive: r∈ S.ND.IS): r∈ A.Nj.ND.IS:= by
 obtain ⟨B,hB,hBa⟩:=(S.ND.xO _ r).mp hActive
 apply (A.Nj.ND.xO _ r).mpr
 by_cases hr: r=R.root
 · subst r
   obtain ⟨C,hC,hP,hm,he,hh⟩:= A.EG
   exact ⟨C,hC,by simp [hP]⟩
 · cases A with
   | single hOwner =>
     refine ⟨B,?_,hBa⟩
     change Function.update S.ND.state R.root _ r=some B
     rw [Function.update_of_ne hr]
     exact hB
   | @inactive beta D C hC hAT hBT hSt hTarget hInactive =>
     by_cases hrb: r=beta
     · subst r
       have hBC: B=C:= Option.some.inj (hB.symm.trans hC)
       subst B
       change ∃Q,S.ND.E2 _ _ beta=some Q∧ Q.active.isSome
       rw [G8.E3]
       exact ⟨_,rfl,hBa⟩
     · refine ⟨B,?_,hBa⟩
       change S.ND.E2 _ _ r=some B
       rw [S.ND.C0 _ _ r hr hrb]
       exact hB
   | @active beta D C hC hAT hBT hSt hTarget hAct =>
     by_cases hrb: r=beta
     · subst r
       change ∃Q,S.ND.E2 _ _ beta=some Q∧ Q.active.isSome
       rw [G8.E3]
       exact ⟨_,rfl,rfl⟩
     · refine ⟨B,?_,hBa⟩
       change S.ND.E2 _ _ r=some B
       rw [S.ND.C0 _ _ r hr hrb]
       exact hB
lemma M3.qO {mode: Bool} (h: M3 mode x y S T) (r: Fin N)
   (hAlive: r∉ T.Nm) (hActive: r∈ S.ND.IS): r∈ T.ND.IS:= by
 cases h with
 | augmentation R hflag =>
   have hLeft: r≠R.ME:= by
     intro heq;subst r
     exact hAlive (mem_union_right _ (mem_union_left _ R.left.tree.MU))
   have hRight: r≠R.L7:= by
     intro heq;subst r
     exact hAlive (mem_union_right _ (mem_union_right _ R.right.tree.MU))
   obtain ⟨A,hA,hAct⟩:=(S.ND.xO _ r).mp hActive
   apply ((S.sE R).ND.xO _ r).mpr
   refine ⟨A,?_,hAct⟩
   change (if r∈({R.ME,R.L7}:Finset (Fin N)) then none else S.ND.state r)=some A
   simp only [mem_insert,mem_singleton,hLeft,hRight,or_self,if_false]
   exact hA
 | extension hmode R hNo A => exact A.qO r hActive
 | skip hNo hNoExt => exact hActive
lemma M2.qO {mode: Bool} {es: List (Fin N ×Fin N)}
   (h: M2 mode es S T) (r: Fin N) (hAlive: r∉ T.Nm)
   (hActive: r∈ S.ND.IS): r∈ T.ND.IS:= by
 induction h with
 | nil => exact hActive
 | cons step rest ih =>
   exact ih hAlive (step.qO r (fun hr=> hAlive (rest.In hr)) hActive)
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma G8.Bm (F: G8 G M)
   (f:∀r,Lp G M r→ Lp G M r)
   (hv:∀r R,(f r R).tree.vertices=R.tree.vertices)
   (ha:∀r R,(f r R).active=R.active) (r: Fin N) (h: r∈F.IS):
   r∈(F.LU f hv).IS:= by
 obtain ⟨R,hR,hAct⟩:=(F.xO _ r).mp h
 apply ((F.LU f hv).xO _ r).mpr
 refine ⟨f r R,?_,?_⟩
 · change (F.state r).map (f r)=some (f r R)
   rw [hR];rfl
 · rw [ha];exact hAct
lemma Lp.fS {r: Fin N} (R: Lp G M r)
   (hActive: R.active.isSome) (hLost:¬R.zS.active.isSome):
   ∃P,R.active=some P∧ P.length=0∧ R.NU=false∧ R.modified=false:= by
 have hflags:(R.NU|| R.modified)=false:= by
   cases hf:(R.NU|| R.modified) with
   | false => rfl
   | true =>
     exfalso
     apply hLost
     simpa only [zS,hf,if_true] using hActive
 have hHeld: R.NU=false:= by cases hh:R.NU<;> cases hm:R.modified<;> simp_all
 have hMod: R.modified=false:= by cases hh:R.NU<;> cases hm:R.modified<;> simp_all
 cases hP: R.active with
 | none => simp [hP] at hActive
 | some P =>
   refine ⟨P,rfl,?_,hHeld,hMod⟩
   by_contra hn
   have hp: 0<P.length:= by omega
   apply hLost
   simp [zS,hHeld,hMod,backtrack,hP,hp]
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell} {x y: Fin N}
lemma Bb.c1 {R: y7 S x y} (A: Bb R)
   {r: Fin N} (hNo: r∉S.ND.IS) (Q: Lp G M r)
   (hQ: A.Nj.ND.state r=some Q):
   ∃B,S.ND.state r=some B∧ Q.tree.vertices ⊆B.tree.vertices:= by
 have hne: r≠R.root:= by
   intro heq;subst r
   exact hNo ((S.ND.xO _ R.root).mpr ⟨R.state,R.present,by simp [R.Lq]⟩)
 cases A with
 | single hOwner =>
   change Function.update S.ND.state R.root _ r=some Q at hQ
   rw [Function.update_of_ne hne] at hQ
   exact ⟨Q,hQ,subset_refl _⟩
 | @inactive beta D B hB hAT hBT hSt hTarget hInactive =>
   by_cases hrb: r=beta
   · subst r
     change S.ND.E2 _ _ beta=some Q at hQ
     rw [S.ND.E3] at hQ
     cases Option.some.inj hQ
     refine ⟨B,hB,?_⟩
     rw [hBT]
     exact D.fK D.HW
   · change S.ND.E2 _ _ r=some Q at hQ
     rw [S.ND.C0 _ _ r hne hrb] at hQ
     exact ⟨Q,hQ,subset_refl _⟩
 | @active beta D B hB hAT hBT hSt hTarget hActive =>
   have hrb: r≠beta:= by
     intro heq;subst r
     exact hNo ((S.ND.xO _ beta).mpr ⟨B,hB,by simp [hActive]⟩)
   change S.ND.E2 _ _ r=some Q at hQ
   rw [S.ND.C0 _ _ r hne hrb] at hQ
   exact ⟨Q,hQ,subset_refl _⟩
lemma M3.c1 {mode: Bool} (h: M3 mode x y S T)
   {r: Fin N} (hNo: r∉S.ND.IS) (Q: Lp G M r)
   (hQ: T.ND.state r=some Q):
   ∃B,S.ND.state r=some B∧ Q.tree.vertices ⊆B.tree.vertices:= by
 cases h with
 | augmentation R hflag =>
   change (if r∈({R.ME,R.L7}:Finset (Fin N)) then none else S.ND.state r)=some Q at hQ
   split_ifs at hQ
   exact ⟨Q,hQ,subset_refl _⟩
 | extension hmode R hNoAug A => exact A.c1 hNo Q hQ
 | skip hNo hNoExt => exact ⟨Q,hQ,subset_refl _⟩
lemma M2.c1 {mode: Bool} {es: List (Fin N ×Fin N)}
   (h: M2 mode es S T) {r: Fin N} (hNo: r∉S.ND.IS) (Q: Lp G M r)
   (hQ: T.ND.state r=some Q):
   ∃B,S.ND.state r=some B∧ Q.tree.vertices ⊆B.tree.vertices:= by
 induction h with
 | nil => exact ⟨Q,hQ,subset_refl _⟩
 | @cons x y es S U T step rest ih =>
   have hNoU: r∉U.ND.IS:= fun ha=> hNo (step.qP ha)
   obtain ⟨C,hC,hQC⟩:= ih hNoU hQ
   obtain ⟨B,hB,hCB⟩:= step.c1 hNo C hC
   exact ⟨B,hB,hQC.trans hCB⟩
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma Bi.oD {alpha beta: Fin N}
   (A: Bi G M alpha) (B: Bi G M beta)
   (hDis: Disjoint A.vertices B.vertices) (e: Fin N ×Fin N) (hReach: A.Reaches e)
   (hG: G.Adj e.2 beta):
   Nonempty (C3 (Mv G ((A.NS∪B.NS)∪{(e.2,beta)})) M):= by
 obtain ⟨P,hP,hEnd⟩:= hReach
 let C:=(A.NS∪B.NS)∪{(e.2,beta)}
 have hSub: Mv G A.NS≤ Mv G C:= by
   apply Fs
   intro e he
   exact mem_union_left _ (mem_union_left _ he)
 let P':= P.NM hSub
 let Q:= v9.trivial (Mv G C) M beta B.L9
 have hPhead: P.vertex (2*P.length)=e.2:= by
   have hh:= congrArg Prod.snd hEnd
   change P.vertex (2*(P.length-1)+2)=e.2 at hh
   rwa [show 2*(P.length-1)+2=2*P.length by omega] at hh
 have hQS: Q.support ⊆B.vertices:= by
   intro v hv
   have hvb: v=beta:= by simpa [Q,v9.support,v9.trivial] using hv
   rw [hvb];exact B.MU
 have hd: Disjoint P'.support Q.support:= hDis.mono (A.nD P) hQS
 have hBridge:(Mv G C).Adj (P'.vertex (2*P'.length)) (Q.vertex (2*Q.length)):= by
   change G.Adj (P.vertex (2*P.length)) beta∧((P.vertex (2*P.length),beta)∈C∨(beta,P.vertex (2*P.length))∈C)
   rw [hPhead]
   exact ⟨hG,Or.inl (mem_union_right _ (mem_singleton_self _))⟩
 have hM:¬M.Adj (P'.vertex (2*P'.length)) (Q.vertex (2*Q.length)):= fun hm=>B.L9 _ hm.symm
 exact ⟨P'.Ac Q hd hBridge hM⟩
lemma tI.q6 (S: tI G M ell)
   (hNo: S.ND.n8 S.NV) (r: Fin N) (hFree:∀w,¬M.Adj r w)
   (hAlive: r∉S.Nm) (e: Fin N ×Fin N) (s: Fin N) (A: Lp G M s)
   (hA: S.ND.state s=some A) (hReach: A.tree.Reaches e) (hEdge: S.NV.Adj e.2 r): s=r:= by
 by_contra hne
 obtain ⟨B,hB⟩:= S.Iu r hFree hAlive
 exact hNo s r hne A B hA hB e.2 r hEdge (A.tree.yG e hReach).2 B.tree.MU
   (fun hm=>hFree _ hm.symm) (A.tree.oD B.tree
     (S.ND.disjoint s r hne A B hA hB) e hReach (S.MF hEdge))
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma tI.bI (S: tI G M ell)
   (hInternal: S.zA) (hNo: S.ND.n8 S.NV)
   {r: Fin N} (P: v9 G M r) (hP: 1<P.length)
   (hLive:∀j,j<2*P.length→ S.NV.Adj (P.vertex j) (P.vertex (j+1)))
   (hSettled:∀j,j+1<P.length→ S.ND.IP (P.KA j))
   (hLast: S.ND.M7 (P.KA (P.length-1)).swap):
   ∃A: Lp G M r,S.ND.state r=some A∧ P.support⊆A.tree.vertices:= by
 let C:= P.F8 0 (by omega)
 have hC: C.length=P.length:= by change P.length-0=P.length;omega
 have hArc (j: ℕ): C.KA j=P.KA j:= by rw [P.xI,Nat.zero_add]
 have hCLive:= P.uQ 0 (by omega) S.NV hLive
 obtain ⟨s,A,hA,hFwd,hRev⟩:= hSettled 0 (by omega)
 have hRootAlive: r∉S.Nm:= by
   have hh:=(S.HK _ _ (hLive 0 (by omega))).1
   rwa [P.first] at hh
 have hEdge: S.NV.Adj (P.KA 0).swap.2 r:= by
   change S.NV.Adj (P.vertex 1) r
   simpa only [P.first] using (hLive 0 (by omega)).symm
 have hOwner:= S.q6 hNo r P.L9 hRootAlive (P.KA 0).swap s A hA hRev hEdge
 subst s
 have hSettledC:∀j,j+1<C.length→ S.ND.IP (C.KA j):= by
   intro j hj;rw [hArc];exact hSettled j (by omega)
 have hLastC: S.ND.M7 (C.KA (C.length-1)).swap:= by rw [hC,hArc];exact hLast
 have hData:= S.oM hInternal hNo C
   (by rw [hArc];exact ⟨r,A,hA,hFwd⟩) (fun j _ hj=>hSettledC j hj) hLastC hCLive
 have hFirst:(C.KA 0).1∈A.tree.vertices:= by rw [hArc];exact (A.tree.yG _ hFwd).1
 have hSupport:= S.ND.e5 S.MG C hData.1 A hA hFirst
 refine ⟨A,hA,?_⟩
 intro v hv
 obtain ⟨i,hi,rfl⟩:= mem_image.mp hv
 have hi': i≤2*P.length:= by have hh:=mem_range.mp hi;omega
 by_cases hz: i=0
 · rw [hz,P.first];exact A.tree.MU
 · have hh:= hSupport (C.mem_support (i-1) (by omega))
   change P.vertex (2*0+1+(i-1))∈A.tree.vertices at hh
   simpa only [show 2*0+1+(i-1)=i by omega] using hh
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
namespace C3
variable (P: C3 G M)
def F1: v9 G M (P.vertex 0) where
 length:= P.length
 vertex:= P.vertex
 first:= rfl
 injective:= fun i j hi hj he=>P.injective i j (by omega) (by omega) he
 Mu:= fun i hi=>P.Mu i hi.le
 MG:= fun i hi=>P.MG i hi.le
 L9:= P.Ki
def GC (k: ℕ) (hk: k≤P.length): v9 G M (P.vertex (2*P.length+1)) where
 length:= k
 vertex i:= P.vertex (2*P.length+1-i)
 first:= by rw [Nat.sub_zero]
 injective:= by
   intro i j hi hj he
   have hh:= P.injective (2*P.length+1-i) (2*P.length+1-j) (by omega) (by omega) he
   omega
 Mu:= by
   intro i hi
   have hh:=(P.Mu (2*P.length+1-(i+1)) (by omega)).symm
   convert hh using 1<;> congr 1<;> omega
 MG:= by
   intro i hi
   have hh:= P.MG (2*P.length+1-(i+1)) (by omega)
   have hp: Odd (2*P.length+1-(i+1))↔ Odd i:= by simp only [Nat.odd_iff];omega
   have hm: M.Adj (P.vertex (2*P.length+1-(i+1)+1)) (P.vertex (2*P.length+1-(i+1)))↔ Odd i:=
     (M.adj_comm _ _).trans (hh.trans hp)
   rw [show 2*P.length+1-(i+1)+1=2*P.length+1-i by omega] at hm
   exact hm
 L9:= P.LP
def Nq (H: SimpleGraph (Fin N)) (h:∀i,i≤2*P.length→ H.Adj (P.vertex i) (P.vertex (i+1))): C3 H M where
 length:= P.length
 vertex:= P.vertex
 injective:= P.injective
 Mu:= h
 MG:= P.MG
 Ki:= P.Ki
 LP:= P.LP
end C3
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma tI.bV (S: tI G M ell)
   (hInternal: S.zA) {r: Fin N} (A: Lp G M r)
   (hA: S.ND.state r=some A) (P: v9 G M r)
   (hVertices: P.support⊆A.tree.vertices)
   (hLive:∀j,j<2*P.length→ S.NV.Adj (P.vertex j) (P.vertex (j+1))): P.Nv A.tree.NS:= by
 let Q:= P.Nq (Mv G A.tree.NS) (fun j hj=>S.o3 hInternal A hA _ _
   (hLive j hj) (hVertices (P.mem_support j (by omega))) (hVertices (P.mem_support (j+1) (by omega))))
 exact S.complete r A hA Q
lemma C3.vP (P: C3 G M)
   (S: tI G M ell)
   (hLive:∀j,j≤2*P.length→ S.NV.Adj (P.vertex j) (P.vertex (j+1)))
   (k: ℕ) (hk: k≤P.length):
   ∀j,j<2*(P.GC k hk).length→
     S.NV.Adj ((P.GC k hk).vertex j) ((P.GC k hk).vertex (j+1)):= by
 intro j hj
 have hh:=(hLive (2*P.length+1-(j+1)) (by change j<2*k at hj;omega)).symm
 change S.NV.Adj (P.vertex (2*P.length+1-j)) (P.vertex (2*P.length+1-(j+1)))
 have hj': j<2*k:= hj
 rw [show 2*P.length+1-(j+1)+1=2*P.length+1-j by omega] at hh
 exact hh
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma tI.pX (S: tI G M ell)
   (hInternal: S.zA) (hNo: S.ND.n8 S.NV)
   (P: C3 G M)
   (hLive:∀j,j≤2*P.length→ S.NV.Adj (P.vertex j) (P.vertex (j+1)))
   (hReached:∀j,j<P.length→ S.ND.M7 (P.F1.KA j))
   (B: Lp G M (P.vertex (2*P.length+1)))
   (hB: S.ND.state (P.vertex (2*P.length+1))=some B):
   ∀k,∀hk: k≤P.length,(P.GC k hk).support⊆B.tree.vertices:= by
 intro k
 induction k with
 | zero =>
   intro hk v hv
   have he: v=P.vertex (2*P.length+1):= by
     simpa [C3.GC,v9.support] using hv
   rw [he];exact B.tree.MU
 | succ k ih =>
   intro hk
   have hk0: k≤P.length:= by omega
   let Q:= P.GC k hk0
   have hQSupport: Q.support⊆B.tree.vertices:= ih hk0
   have hQLive:= P.vP S hLive k hk0
   have hInside:= S.bV hInternal B hB Q hQSupport hQLive
   let i:= P.length-1-k
   have hi: i<P.length:= by dsimp [i];omega
   obtain ⟨s,A,hA,hReach⟩:= hReached i hi
   have hLastAlive: P.vertex (2*P.length+1)∉S.Nm:= S.vI _ B hB
   have hOwner: s=P.vertex (2*P.length+1):= by
     by_cases hkZ: k=0
     · have hEdge: S.NV.Adj (P.F1.KA i).2 (P.vertex (2*P.length+1)):= by
         have hh:= hLive (2*i+2) (by dsimp [i];omega)
         change S.NV.Adj (P.vertex (2*i+2)) (P.vertex (2*P.length+1))
         convert hh using 1<;> congr 1<;> dsimp [i]<;> omega
       exact S.q6 hNo _ P.LP hLastAlive _ s A hA hReach hEdge
     · have hkPos: 0<Q.length:= by change 0<k;omega
       let e:= Q.KA (Q.length-1)
       have hQR: B.tree.Reaches e:=⟨Q.Kt B.tree.NS hInside,hkPos,rfl⟩
       have hQHead: e.2=P.vertex (2*i+3):= by
         change P.vertex (2*P.length+1-(2*(k-1)+2))=P.vertex (2*i+3)
         congr 1
         dsimp [i];omega
       have hEdge: S.NV.Adj e.2 (P.F1.KA i).2:= by
         rw [hQHead]
         have hh:=(hLive (2*i+2) (by dsimp [i];omega)).symm
         exact hh
       have hUnmatched:¬M.Adj e.2 (P.F1.KA i).2:= by
         rw [hQHead]
         change ¬M.Adj (P.vertex (2*i+3)) (P.vertex (2*i+2))
         intro hm
         have hh:=(P.MG (2*i+2) (by dsimp [i];omega)).mp hm.symm
         rw [Nat.odd_iff] at hh
         omega
       have hsame:= S.ND.nO S.NV S.MF hNo
         (P.vertex (2*P.length+1)) s e (P.F1.KA i) ⟨B,hB,hQR⟩ ⟨A,hA,hReach⟩ hEdge hUnmatched
       exact hsame.symm
   subst s
   have hAB: A=B:= Option.some.inj (hA.symm.trans hB)
   subst A
   have hEnds:= B.tree.yG (P.F1.KA i) hReach
   intro v hv
   obtain ⟨j,hj,rfl⟩:= mem_image.mp hv
   have hj': j≤2*(k+1):= by
     have hh:=mem_range.mp hj
     change j<2*(k+1)+1 at hh
     omega
   by_cases hOld: j≤2*k
   · exact hQSupport (Q.mem_support j hOld)
   · rcases (show j=2*k+1∨ j=2*k+2 by omega) with hjEq|hjEq
     · subst j
       have he:(P.GC (k+1) hk).vertex (2*k+1)=(P.F1.KA i).2:= by
         change P.vertex (2*P.length+1-(2*k+1))=P.vertex (2*i+2)
         congr 1
         dsimp [i];omega
       rw [he];exact hEnds.2
     · subst j
       have he:(P.GC (k+1) hk).vertex (2*k+2)=(P.F1.KA i).1:= by
         change P.vertex (2*P.length+1-(2*k+2))=P.vertex (2*i+1)
         congr 1
         dsimp [i];omega
       rw [he];exact hEnds.1
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma tI.b2 (S: tI G M ell)
   (hInternal: S.zA) (hNo: S.ND.n8 S.NV)
   (P: C3 G M)
   (hLive:∀j,j≤2*P.length→ S.NV.Adj (P.vertex j) (P.vertex (j+1)))
   (hReached:∀j,j<P.length→ S.ND.M7 (P.F1.KA j)): False:= by
 have hFirstAlive: P.vertex 0∉S.Nm:=(S.HK _ _ (hLive 0 (by omega))).1
 have hLastAlive: P.vertex (2*P.length+1)∉S.Nm:=(S.HK _ _ (hLive (2*P.length) le_rfl)).2
 obtain ⟨A,hA⟩:= S.Iu (P.vertex 0) P.Ki hFirstAlive
 obtain ⟨B,hB⟩:= S.Iu (P.vertex (2*P.length+1)) P.LP hLastAlive
 have hDistinct: P.vertex 0≠P.vertex (2*P.length+1):= by
   intro he
   have hh:= P.injective 0 (2*P.length+1) (by omega) le_rfl he
   omega
 by_cases hZero: P.length=0
 · have hOne: P.vertex 1=P.vertex (2*P.length+1):= by rw [hZero]
   have hBridge: S.NV.Adj (P.vertex 0) (P.vertex (2*P.length+1)):= by
     have hh:=hLive 0 (by omega)
     rwa [hOne] at hh
   let C:=(A.tree.NS∪B.tree.NS)∪{(P.vertex 0,P.vertex (2*P.length+1))}
   have hMemory:∀j,j≤2*P.length→(Mv G C).Adj (P.vertex j) (P.vertex (j+1)):= by
     intro j hj
     have hj0: j=0:= by omega
     subst j
     change G.Adj (P.vertex 0) (P.vertex 1)∧((P.vertex 0,P.vertex 1)∈C∨(P.vertex 1,P.vertex 0)∈C)
     rw [hOne]
     exact ⟨S.MF hBridge,Or.inl (mem_union_right _ (mem_singleton_self _))⟩
   exact hNo _ _ hDistinct A B hA hB _ _ hBridge A.tree.MU B.tree.MU (P.Ki _)
     ⟨P.Nq (Mv G C) hMemory⟩
 · have hPositive: 0<P.length:= by omega
   let Q:= P.GC P.length le_rfl
   have hSupport:= S.pX hInternal hNo P hLive hReached B hB P.length le_rfl
   have hInside:= S.bV hInternal B hB Q hSupport
     (P.vP S hLive P.length le_rfl)
   let e:= Q.KA (Q.length-1)
   have hReach: B.tree.Reaches e:=⟨Q.Kt B.tree.NS hInside,hPositive,rfl⟩
   have hHead: e.2=P.vertex 1:= by
     change P.vertex (2*P.length+1-(2*(P.length-1)+2))=P.vertex 1
     congr 1
     omega
   have hEdge: S.NV.Adj e.2 (P.vertex 0):= by
     rw [hHead]
     exact (hLive 0 (by omega)).symm
   have hOwner:= S.q6 hNo _ P.Ki hFirstAlive e _ B hB hReach hEdge
   exact hDistinct hOwner.symm
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
namespace G8
variable (F: G8 G M)
def Fo: Finset (Fin N):=
 F.IS.biUnion (fun r=>(F.state r).elim ∅ (fun R=>R.Dg))
lemma xM (v: Fin N): v∈F.Fo↔
   ∃(r: Fin N) (R: Lp G M r) (P: v9 G M r),
     F.state r=some R∧ R.active=some P∧ v∈P.support:= by
 constructor
 · intro hv
   obtain ⟨r,hr,hv⟩:= mem_biUnion.mp hv
   cases hR:F.state r with
   | none => simp [hR] at hv
   | some R =>
     cases hP:R.active with
     | none => simp [hR,Lp.Dg,hP] at hv
     | some P =>
       exact ⟨r,R,P,hR,hP,by simpa [hR,Lp.Dg,hP] using hv⟩
 · rintro ⟨r,R,P,hR,hP,hv⟩
   apply mem_biUnion.mpr
   refine ⟨r,(F.xO _ r).mpr ⟨R,hR,by simp [hP]⟩,?_⟩
   simpa [hR,Lp.Dg,hP] using hv
lemma lJ (r: Fin N) (h: r∈F.IS): r∈F.Fo:= by
 obtain ⟨R,hR,ha⟩:=(F.xO _ r).mp h
 cases hP:R.active with
 | none => simp [hP] at ha
 | some P => exact (F.xM r).mpr ⟨r,R,P,hR,hP,P.MU⟩
lemma tJ (e: Fin N ×Fin N) (h: F.Lh e): e.1∈F.Fo:= by
 obtain ⟨k,r,R,hR,P,i,hP,hi,hik,hie,havoid⟩:= h
 apply (F.xM e.1).mpr
 refine ⟨r,R,P,hR,hP,?_⟩
 rw [←hie]
 exact P.mem_support (2*i+1) (by omega)
lemma f0 (ell: ℕ) (lab: Fin N ×Fin N→ ℕ) (h: F.Mq ell lab):
   F.Fo.card≤(2*ell+1)*F.IS.card:= by
 have hEach:∀r∈F.IS,((F.state r).elim ∅ (fun R=>R.Dg)).card≤2*ell+1:= by
   intro r hr
   obtain ⟨R,hR,ha⟩:=(F.xO _ r).mp hr
   simp only [hR,Option.elim_some]
   exact R.oB ell lab (h r R hR)
 calc
   F.Fo.card≤∑r∈F.IS,((F.state r).elim ∅ (fun R=>R.Dg)).card:= card_biUnion_le
   _≤∑_∈F.IS,(2*ell+1):= sum_le_sum hEach
   _=(2*ell+1)*F.IS.card:= by simp [Nat.mul_comm]
end G8
namespace C3
variable (P: C3 G M)
lemma mem_support (i: ℕ) (hi: i≤2*P.length+1): P.vertex i∈P.support:=
 mem_image.mpr ⟨i,mem_range.mpr (by omega),rfl⟩
end C3
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
namespace G8
def De (F H: G8 G M): Prop:=
 ∀r R,H.state r=some R→ R.extended=false→
   ∃B,F.state r=some B∧ B.extended=false∧ R.tree.vertices⊆B.tree.vertices∧ R.NU=B.NU
lemma s2 (F: G8 G M): De F F:= by
 intro r R hR he
 exact ⟨R,hR,he,subset_refl _,rfl⟩
lemma De.trans {F H K: G8 G M} (hFH: De F H) (hHK: De H K):
   De F K:= by
 intro r R hR he
 obtain ⟨C,hC,hCe,hRC,hRH⟩:= hHK r R hR he
 obtain ⟨B,hB,hBe,hCB,hCH⟩:= hFH r C hC hCe
 exact ⟨B,hB,hBe,hRC.trans hCB,hRH.trans hCH⟩
lemma qA (F H: G8 G M) {a: Fin N} (A: Lp G M a)
   (hEq: H.state=Function.update F.state a (some A)) (hA: A.extended=true): De F H:= by
 intro r R hR he
 rw [hEq] at hR
 by_cases hr: r=a
 · subst r
   rw [Function.update_self] at hR
   cases Option.some.inj hR
   rw [hA] at he
   cases he
 · rw [Function.update_of_ne hr] at hR
   exact ⟨R,hR,he,subset_refl _,rfl⟩
lemma qB (F H: G8 G M) {a b: Fin N} (hab: a≠b)
   (B: Lp G M b) (hB: F.state b=some B) (A': Lp G M a) (B': Lp G M b)
   (hEq: H.state=F.E2 A' B') (hA: A'.extended=true)
   (hBB: B'.extended=false→ B.extended=false∧ B'.tree.vertices⊆B.tree.vertices∧ B'.NU=B.NU): De F H:= by
 intro r R hR he
 rw [hEq] at hR
 by_cases hra: r=a
 · subst r
   rw [F.CZ hab] at hR
   cases Option.some.inj hR
   rw [hA] at he
   cases he
 · by_cases hrb: r=b
   · subst r
     rw [F.E3] at hR
     cases Option.some.inj hR
     obtain ⟨heB,hv,hh⟩:= hBB he
     exact ⟨B,hB,heB,hv,hh⟩
   · rw [F.C0 A' B' r hra hrb] at hR
     exact ⟨R,hR,he,subset_refl _,rfl⟩
end G8
variable {ell: ℕ} {S T: tI G M ell} {x y: Fin N}
lemma Bb.CV {R: y7 S x y} (A: Bb R):
   G8.De S.ND A.Nj.ND:= by
 cases A with
 | single hOwner => exact G8.qA S.ND _ _ rfl rfl
 | inactive D B hB hAT hBT hSt hTarget hInactive =>
   apply G8.qB S.ND _ D.distinct B hB _ _ rfl rfl
   intro he
   refine ⟨he,?_,rfl⟩
   rw [hBT]
   exact D.fK D.HW
 | active D B hB hAT hBT hSt hTarget hActive =>
   apply G8.qB S.ND _ D.data.distinct B hB _ _ rfl rfl
   intro he
   refine ⟨he,?_,rfl⟩
   rw [hBT]
   change ((Classical.choice D.transfer).right.FX D.data.KC _).normalized.vertices ⊆D.data.right.vertices
   rw [Bi.r8,Bi.kK,(Classical.choice D.transfer).MT]
   exact D.data.right.g6 _
lemma M3.CV {mode: Bool} (h: M3 mode x y S T): G8.De S.ND T.ND:= by
 cases h with
 | augmentation A hflag =>
   intro r R hR he
   change (if r∈({A.ME,A.L7}:Finset (Fin N)) then none else S.ND.state r)=some R at hR
   split_ifs at hR
   exact ⟨R,hR,he,subset_refl _,rfl⟩
 | extension hmode R hNo A => exact A.CV
 | skip hNo hNoExt => exact G8.s2 S.ND
lemma M2.CV {mode: Bool} {es: List (Fin N ×Fin N)} (h: M2 mode es S T):
   G8.De S.ND T.ND:= by
 induction h with
 | nil => exact G8.s2 _
 | cons step rest ih => exact step.CV.trans ih
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
namespace G8
def Lm (F: G8 G M) (limit: ℕ): Prop:=
 ∀r R,F.state r=some R→ limit≤R.tree.vertices.card→ R.NU=true
end G8
lemma Lp.eT {r: Fin N} (R: Lp G M r):
   R.zS.tree.vertices=R.tree.vertices:= by unfold zS;split_ifs<;> rfl
lemma Lp.mC {r: Fin N} (R: Lp G M r):
   R.zS.NU=R.NU:= by unfold zS;split_ifs<;> rfl
lemma M2.lA {S T: tI G M ell} {limit: ℕ}
   (hSound: S.ND.Lm limit) {es: List (Fin N ×Fin N)}
   (h: M2 true es (S.IX limit) T) {x y: Fin N} (R: y7 T x y):
   R.state.tree.vertices.card<limit:= by
 obtain ⟨B,hB,hBe,hVertices,hHeld⟩:= h.CV R.root R.state R.present R.H9
 change (S.ND.state R.root).map (fun A=>A.IX limit)=some B at hB
 obtain ⟨A,hA,hAB⟩:= Option.map_eq_some_iff.mp hB
 have hAHeld:(A.IX limit).NU=false:= by rw [hAB];exact hHeld.symm.trans R.MK
 have hSmall: A.tree.vertices.card<limit:= by
   by_contra hn
   have hBig: limit≤A.tree.vertices.card:= by omega
   have hHeldA:= hSound R.root A hA hBig
   change (A.NU&& decide (limit≤A.tree.vertices.card))=false at hAHeld
   simp [hHeldA,hBig] at hAHeld
 have hCard:= card_le_card hVertices
 rw [←hAB] at hCard
 change R.state.tree.vertices.card≤A.tree.vertices.card at hCard
 omega
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
namespace v9
variable {r: Fin N} (P: v9 G M r)
def IG (i: ℕ): Fin N ×Fin N:=(P.vertex (2*i),P.vertex (2*i+1))
def GW: Finset (Fin N ×Fin N):=(range P.length).image P.IG
lemma v2: P.GW.card≤P.length:=(card_image_le).trans_eq (card_range _)
end v9
namespace G8
def y4 (F: G8 G M) (E: Finset (Fin N ×Fin N)): Prop:=
 ∀e∈E,∀r R,F.state r=some R→ e.1∈R.tree.vertices→ e.2∈R.tree.vertices→
   ∃P,R.active=some P∧ e∈P.GW
def D0 (F: G8 G M) (E: Finset (Fin N ×Fin N))
   {r: Fin N} (R: Lp G M r): Finset (Fin N ×Fin N):=
 E.filter (fun e=>e.1∈R.tree.vertices∧ e.2∈R.tree.vertices)
lemma rK (F: G8 G M) (E: Finset (Fin N ×Fin N))
   (h: F.y4 E) (ell: ℕ) (lab: Fin N ×Fin N→ ℕ) (hLabel: F.Mq ell lab)
   {r: Fin N} (R: Lp G M r) (hR: F.state r=some R):
   (F.D0 E R).card≤ell:= by
 cases hP:R.active with
 | none =>
   have heq: F.D0 E R=∅:= by
     apply eq_empty_iff_forall_notMem.mpr
     intro e he
     obtain ⟨he,hv,hv'⟩:= mem_filter.mp he
     obtain ⟨P,hActive,hUn⟩:= h e he r R hR hv hv'
     rw [hP] at hActive
     cases hActive
   rw [heq,card_empty]
   omega
 | some P =>
   have hSub: F.D0 E R⊆P.GW:= by
     intro e he
     obtain ⟨he,hv,hv'⟩:= mem_filter.mp he
     obtain ⟨Q,hQ,hUn⟩:= h e he r R hR hv hv'
     have hQP: Q=P:= Option.some.inj (hQ.symm.trans hP)
     rwa [hQP] at hUn
   exact (card_le_card hSub).trans (P.v2.trans (hLabel r R hR P hP).1)
end G8
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell} {x y: Fin N}
namespace G8
def C6 (F: G8 G M) (v: Fin N): Prop:=
 F.Mn (fun _ R=>R.extended=true∧ v∈R.tree.vertices)
lemma bS (F: G8 G M) (v: Fin N) (hv: F.C6 v)
   {r: Fin N} (R: Lp G M r) (hR: F.state r=some R) (he: R.extended=false): v∉R.tree.vertices:= by
 obtain ⟨s,A,hA,hAe,hAv⟩:= hv
 intro hRv
 have hsr:= F.BE s r v ⟨A,hA,hAv⟩ ⟨R,hR,hRv⟩
 subst s
 have hAR: A=R:= Option.some.inj (hA.symm.trans hR)
 subst A
 rw [he] at hAe
 cases hAe
end G8
lemma Bb.e0 {R: y7 S x y} (A: Bb R)
   (v: Fin N) (hv: S.ND.C6 v): A.Nj.ND.C6 v:= by
 cases A with
 | single hOwner =>
   apply G8.t8 S.ND _ (fun _ B=>B.extended=true∧ v∈B.tree.vertices)
     R.state _ R.present rfl _ hv
   rintro ⟨he,hMem⟩
   rw [R.H9] at he
   cases he
 | inactive D B hB hAT hBT hSt hTarget hInactive =>
   apply G8.t9 S.ND _ (fun _ C=>C.extended=true∧ v∈C.tree.vertices)
     D.distinct R.state B R.present hB _ _ rfl _ _ hv
   · rintro ⟨he,hMem⟩
     rw [R.H9] at he
     cases he
   · rintro ⟨he,hMem⟩
     have hOld: v∈D.left.vertices∪D.right.vertices:= mem_union_right _ (by rwa [←hBT])
     rw [←D.v8] at hOld
     rcases mem_union.mp hOld with hL|hR
     · left
       exact ⟨rfl,by
         change v∈(D.JM.FX D.KC _).normalized.vertices
         rwa [Bi.r8,Bi.kK]⟩
     · right
       exact ⟨he,by
         change v∈(D.remaining.FX D.KC _).normalized.vertices
         rwa [Bi.r8,Bi.kK]⟩
 | active D B hB hAT hBT hSt hTarget hActive =>
   apply G8.t9 S.ND _ (fun _ C=>C.extended=true∧ v∈C.tree.vertices)
     D.data.distinct R.state B R.present hB _ _ rfl _ _ hv
   · rintro ⟨he,hMem⟩
     rw [R.H9] at he
     cases he
   · rintro ⟨he,hMem⟩
     let Z:= Classical.choice D.transfer
     have hOld: v∈D.data.left.vertices∪D.data.right.vertices:= mem_union_right _ (by rwa [←hBT])
     rw [←Z.vertices] at hOld
     rcases mem_union.mp hOld with hL|hR
     · left
       exact ⟨rfl,by
         change v∈(Z.left.FX D.data.KC _).normalized.vertices
         rwa [Bi.r8,Bi.kK]⟩
     · right
       exact ⟨he,by
         change v∈(Z.right.FX D.data.KC _).normalized.vertices
         rwa [Bi.r8,Bi.kK]⟩
lemma M3.e0 {mode: Bool} (h: M3 mode x y S T)
   (v: Fin N) (hAlive: v∉T.Nm) (hv: S.ND.C6 v): T.ND.C6 v:= by
 cases h with
 | augmentation R hFlag =>
   obtain ⟨r,A,hA,he,hMem⟩:= hv
   by_cases hrL: r=R.ME
   · subst r
     have hEq: A=R.left:= Option.some.inj (hA.symm.trans R.HJ)
     subst A
     exact (hAlive (mem_union_right _ (mem_union_left _ hMem))).elim
   · by_cases hrR: r=R.L7
     · subst r
       have hEq: A=R.right:= Option.some.inj (hA.symm.trans R.GE)
       subst A
       exact (hAlive (mem_union_right _ (mem_union_right _ hMem))).elim
     · refine ⟨r,A,?_,he,hMem⟩
       change (if r∈({R.ME,R.L7}:Finset (Fin N)) then none else S.ND.state r)=some A
       simp only [mem_insert,mem_singleton,hrL,hrR,or_self,if_false]
       exact hA
 | extension hMode R hNo A => exact A.e0 v hv
 | skip hNo hNoExt => exact hv
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
inductive Ll (mode: Bool) (x y: Fin N) (E: Finset (Fin N ×Fin N)):
   tI G M ell→ tI G M ell→ Finset (Fin N ×Fin N)→ Prop where
 | augmentation {S: tI G M ell} (R: qF S x y)
     (hFlag: mode=true→ R.left.extended=false): Ll mode x y E S (S.sE R) E
 | extension {S: tI G M ell} (hMode: mode=true) (R: y7 S x y)
     (hNo:¬S.Bd x y true) (A: Bb R): Ll mode x y E S A.Nj (insert (x,y) E)
 | skip {S: tI G M ell} (hNo:¬S.Bd x y mode)
     (hNoExt: mode=true→¬Nonempty (y7 S x y)): Ll mode x y E S S E
lemma Ll.Mi {mode: Bool} {x y: Fin N} {E E': Finset (Fin N ×Fin N)}
   {S T: tI G M ell} (h: Ll mode x y E S T E'): M3 mode x y S T:= by
 cases h with
 | augmentation R hFlag => exact M3.augmentation R hFlag
 | extension hMode R hNo A => exact M3.extension hMode R hNo A
 | skip hNo hNoExt => exact M3.skip hNo hNoExt
lemma M3.w0 {mode: Bool} {x y: Fin N} {S T: tI G M ell}
   (h: M3 mode x y S T) (E: Finset (Fin N ×Fin N)):∃E',Ll mode x y E S T E':= by
 cases h with
 | augmentation R hFlag => exact ⟨E,Ll.augmentation R hFlag⟩
 | extension hMode R hNo A => exact ⟨insert (x,y) E,Ll.extension hMode R hNo A⟩
 | skip hNo hNoExt => exact ⟨E,Ll.skip hNo hNoExt⟩
namespace tI
def C4 (S: tI G M ell) (E: Finset (Fin N ×Fin N)): Prop:=
 ∀e∈E,∀v,(v=e.1∨ v=e.2)→ v∉S.Nm→ S.ND.C6 v
end tI
lemma Bb.eV {S: tI G M ell} {x y: Fin N}
   {R: y7 S x y} (A: Bb R):
   A.Nj.ND.C6 x∧ A.Nj.ND.C6 y:= by
 obtain ⟨B,hB,hP,hm,hExt,hHeld⟩:= A.EG
 have hX: A.Nf.vertex (2*R.NX.length)=x:=(A.Iz.2 _ le_rfl).trans R.NC
 have hY: A.Nf.vertex (2*R.NX.length+1)=y:= congrArg Prod.fst A.CS
 have hInside:= B.inside A.Nf hP
 constructor
 · refine ⟨R.root,B,hB,hExt,?_⟩
   have hMem:= B.tree.EA A.Nf hInside (A.Nf.mem_support (2*R.NX.length) (by have hh:=A.yY;omega))
   simpa only [hX] using hMem
 · refine ⟨R.root,B,hB,hExt,?_⟩
   have hMem:= B.tree.EA A.Nf hInside (A.Nf.mem_support (2*R.NX.length+1) (by have hh:=A.yY;omega))
   simpa only [hY] using hMem
lemma Ll.LD {mode: Bool} {x y: Fin N} {E E': Finset (Fin N ×Fin N)}
   {S T: tI G M ell} (h: Ll mode x y E S T E')
   (hOld: S.C4 E): T.C4 E':= by
 intro e he v hv hAlive
 cases h with
 | augmentation R hFlag =>
   have hStep:= M3.augmentation R hFlag
   exact hStep.e0 v hAlive (hOld e he v hv (fun hr=>hAlive (hStep.In hr)))
 | extension hMode R hNo A =>
   rcases mem_insert.mp he with he|he
   · subst e
     rcases hv with hv|hv
     · rw [hv];exact A.eV.1
     · rw [hv];exact A.eV.2
   · exact A.e0 v (hOld e he v hv (fun hr=>hAlive ((M3.extension hMode R hNo A).In hr)))
 | skip hNo hNoExt => exact hOld e he v hv hAlive
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma Bb.tQ {S: tI G M ell} {x y: Fin N}
   {R: y7 S x y} (A: Bb R):(x,y)∈A.Nf.GW:= by
 apply mem_image.mpr
 refine ⟨R.NX.length,mem_range.mpr A.yY,?_⟩
 apply Prod.ext
 · exact (A.Iz.2 _ le_rfl).trans R.NC
 · exact congrArg Prod.fst A.CS
namespace C2
variable {alpha beta: Fin N} (D: C2 G M alpha beta)
lemma p6 (i: ℕ) (hi0: D.index≤ i) (hi: i<D.Ng.length):
   ∃n,n<D.path.length∧ D.path.IG n=D.Ng.IG i:= by
 let n:= D.data.NX.length+(i+1-D.index)
 have hp:=D.positive
 have hb:=D.bound
 have hn: n<D.path.length:= by
   change n<D.data.NX.length+(D.Ng.length+1-D.index)
   dsimp [n];omega
 have hLower: D.data.NX.length<n:= by dsimp [n];omega
 refine ⟨n,hn,?_⟩
 apply Prod.ext
 · change D.data.NX.Iy D.Ng D.index (2*n)=D.Ng.vertex (2*i)
   rw [v9.Iy,if_neg (by omega)]
   congr 1
   unfold v9.JH
   dsimp [n];omega
 · change D.data.NX.Iy D.Ng D.index (2*n+1)=D.Ng.vertex (2*i+1)
   rw [v9.Iy,if_neg (by omega)]
   congr 1
   unfold v9.JH
   dsimp [n];omega
lemma lF (i: ℕ) (hi: i<D.index-1):
   D.Ng.IG i∈(D.Ng.take (D.index-1) (by have hb:=D.bound;omega)).GW:= by
 exact mem_image.mpr ⟨i,mem_range.mpr hi,rfl⟩
end C2
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma y7.c9 {S: tI G M ell} {x y: Fin N}
   (R: y7 S x y) (E: Finset (Fin N ×Fin N)) (hE: S.C4 E)
   (e: Fin N ×Fin N) (he: e∈E): e.1∉R.state.tree.vertices∧ e.2∉R.state.tree.vertices:= by
 constructor
 · intro hm
   have ha:= S.k7 R.root R.state R.present _ hm
   exact S.ND.bS e.1 (hE e he e.1 (Or.inl rfl) ha) R.state R.present R.H9 hm
 · intro hm
   have ha:= S.k7 R.root R.state R.present _ hm
   exact S.ND.bS e.2 (hE e he e.2 (Or.inr rfl) ha) R.state R.present R.H9 hm
namespace C2
variable {alpha beta: Fin N} (D: C2 G M alpha beta)
   (Z: IQ D.data.left D.data.right D.path D.data.NX.length D.path.length le_rfl D.NG)
lemma fT (i: ℕ) (hi: i<D.Ng.length)
   (hTail:(D.Ng.IG i).1∈Z.left.vertices): D.Ng.IG i∈D.path.GW:= by
 have hQInside:(D.Ng.take (D.index-1) (by have hb:=D.bound;omega)).Nv Z.right.NS:= by
   rw [Z.MT,D.sI]
   exact D.data.right.lB D.Ng D.inside D.index D.positive (by have hb:=D.bound;omega)
 have hAfter: D.index≤ i:= by
   by_contra hn
   have hi0: i≤D.index-1:= by have hp:=D.positive;omega
   have hm:= Z.right.EA _ hQInside
     ((D.Ng.take (D.index-1) (by have hb:=D.bound;omega)).mem_support (2*i) (by change 2*i≤2*(D.index-1);omega))
   exact disjoint_left.mp Z.disjoint hTail hm
 obtain ⟨n,hn,he⟩:= D.p6 i hAfter hi
 exact mem_image.mpr ⟨n,mem_range.mpr hn,he⟩
lemma eM (i: ℕ) (hi: i<D.Ng.length)
   (hHead:(D.Ng.IG i).2∈Z.right.vertices):
   D.Ng.IG i∈(D.Ng.take (D.index-1) (by have hb:=D.bound;omega)).GW:= by
 have hBefore: i<D.index-1:= by
   by_contra hn
   have hi0: D.index≤ i+1:= by omega
   have hSuffix: D.Ng.KA i∈D.Ng.La D.index:=
     mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_range.mpr hi,hi0⟩,rfl⟩
   rw [←D.sI] at hSuffix
   have hArc:= D.path.jF D.data.NX.length D.path.length le_rfl hSuffix
   obtain ⟨n,hn,he⟩:= mem_image.mp hArc
   have hn':= mem_range.mp hn
   have hm:= Z.left.EA _ Z.active (D.path.mem_support (2*n+1) (by omega))
   change (D.path.KA n).1∈Z.left.vertices at hm
   rw [he] at hm
   exact disjoint_left.mp Z.disjoint hm hHead
 exact D.lF i hBefore
end C2
end Be
end
noncomputable section
namespace Be.G8
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
lemma j0 (F H: G8 G M) (E: Finset (Fin N ×Fin N))
   {a b: Fin N} (hab: a≠b) (A: Lp G M a) (B: Lp G M b)
   (hEq: H.state=F.E2 A B) (hOld: F.y4 E)
   (hA:∀e∈E,e.1∈A.tree.vertices→ e.2∈A.tree.vertices→∃P,A.active=some P∧ e∈P.GW)
   (hB:∀e∈E,e.1∈B.tree.vertices→ e.2∈B.tree.vertices→∃P,B.active=some P∧ e∈P.GW):
   H.y4 E:= by
 intro e he r R hR hv hw
 rw [hEq] at hR
 by_cases hra: r=a
 · subst r
   rw [F.CZ hab] at hR
   cases Option.some.inj hR
   exact hA e he hv hw
 · by_cases hrb: r=b
   · subst r
     rw [F.E3] at hR
     cases Option.some.inj hR
     exact hB e he hv hw
   · rw [F.C0 A B r hra hrb] at hR
     exact hOld e he r R hR hv hw
end Be.G8
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S: tI G M ell} {x y: Fin N} {R: y7 S x y}
lemma Bb.AA (A: Bb R) (E: Finset (Fin N ×Fin N))
   (hEndpoints: S.C4 E) (hOld: S.ND.y4 E):
   A.Nj.ND.y4 E:= by
 cases A with
 | single hOwner =>
   intro e he r Q hQ hv hw
   by_cases hr: r=R.root
   · subst r
     have hAlive: e.1∉S.Nm:=(Bb.single hOwner).Nj.k7 R.root Q hQ _ hv
     obtain ⟨s,B,hB,hExt,hMem⟩:= hEndpoints e he e.1 (Or.inl rfl) hAlive
     have hne: s≠R.root:= by
       intro heq;subst s
       have hBR: B=R.state:= Option.some.inj (hB.symm.trans R.present)
       subst B
       rw [R.H9] at hExt
       cases hExt
     have hBNew:(Bb.single hOwner).Nj.ND.state s=some B:= by
       change Function.update S.ND.state R.root _ s=some B
       rw [Function.update_of_ne hne]
       exact hB
     exact (hne ((Bb.single hOwner).Nj.ND.BE s R.root e.1
       ⟨B,hBNew,hMem⟩ ⟨Q,hQ,hv⟩)).elim
   · change Function.update S.ND.state R.root _ r=some Q at hQ
     rw [Function.update_of_ne hr] at hQ
     exact hOld e he r Q hQ hv hw
 | @inactive beta D B hB hAT hBT hSt hTarget hInactive =>
   apply G8.j0 S.ND _ E D.distinct _ _ rfl hOld
   · intro e he hv hw
     change e.1∈(D.JM.FX D.KC _).normalized.vertices at hv
     change e.2∈(D.JM.FX D.KC _).normalized.vertices at hw
     rw [Bi.r8,Bi.kK] at hv hw
     have hOutside:= R.c9 E hEndpoints e he
     have hV: e.1∈D.right.vertices:= by
       have hh: e.1∈D.left.vertices∪D.right.vertices:= by rw [←D.v8];exact mem_union_left _ hv
       exact (mem_union.mp hh).resolve_left (by rw [←hAT];exact hOutside.1)
     have hW: e.2∈D.right.vertices:= by
       have hh: e.2∈D.left.vertices∪D.right.vertices:= by rw [←D.v8];exact mem_union_left _ hw
       exact (mem_union.mp hh).resolve_left (by rw [←hAT];exact hOutside.2)
     obtain ⟨P,hP,hArc⟩:= hOld e he beta B hB (by rwa [hBT]) (by rwa [hBT])
     obtain ⟨i,hi,hie⟩:= mem_image.mp hArc
     have hi':= mem_range.mp hi
     have hInside: P.Nv D.right.NS:= by rw [←hBT];exact B.inside P hP
     have hRet:= D.right.lC P hInside D.target (hInactive P hP)
     have hMem:= D.remaining.EA P hRet (P.mem_support (2*i) (by omega))
     change (P.IG i).1∈D.remaining.vertices at hMem
     rw [hie] at hMem
     exact (disjoint_left.mp D.p9 hv hMem).elim
   · intro e he hv hw
     change e.1∈(D.remaining.FX D.KC _).normalized.vertices at hv
     change e.2∈(D.remaining.FX D.KC _).normalized.vertices at hw
     rw [Bi.r8,Bi.kK] at hv hw
     have hV:= D.right.g6 {D.target} hv
     have hW:= D.right.g6 {D.target} hw
     obtain ⟨P,hP,hArc⟩:= hOld e he beta B hB (by rwa [hBT]) (by rwa [hBT])
     exact ⟨P,hP,hArc⟩
 | @active beta D B hB hAT hBT hSt hTarget hActive =>
   let Z:= Classical.choice D.transfer
   apply G8.j0 S.ND _ E D.data.distinct _ _ rfl hOld
   · intro e he hv hw
     change e.1∈(Z.left.FX D.data.KC _).normalized.vertices at hv
     change e.2∈(Z.left.FX D.data.KC _).normalized.vertices at hw
     rw [Bi.r8,Bi.kK] at hv hw
     have hOutside:= R.c9 E hEndpoints e he
     have hV: e.1∈D.data.right.vertices:= by
       have hh: e.1∈D.data.left.vertices∪D.data.right.vertices:= by rw [←Z.vertices];exact mem_union_left _ hv
       exact (mem_union.mp hh).resolve_left (by rw [←hAT];exact hOutside.1)
     have hW: e.2∈D.data.right.vertices:= by
       have hh: e.2∈D.data.left.vertices∪D.data.right.vertices:= by rw [←Z.vertices];exact mem_union_left _ hw
       exact (mem_union.mp hh).resolve_left (by rw [←hAT];exact hOutside.2)
     obtain ⟨P,hP,hArc⟩:= hOld e he beta B hB (by rwa [hBT]) (by rwa [hBT])
     have hPP: P=D.Ng:= Option.some.inj (hP.symm.trans hActive)
     subst P
     obtain ⟨i,hi,hie⟩:= mem_image.mp hArc
     have hMem:(D.Ng.IG i).1∈Z.left.vertices:= by rw [hie];exact hv
     have hNew:= D.fT Z i (mem_range.mp hi) hMem
     rw [hie] at hNew
     exact ⟨D.path,rfl,hNew⟩
   · intro e he hv hw
     change e.1∈(Z.right.FX D.data.KC _).normalized.vertices at hv
     change e.2∈(Z.right.FX D.data.KC _).normalized.vertices at hw
     rw [Bi.r8,Bi.kK] at hv hw
     have hSubset: Z.right.vertices⊆D.data.right.vertices:= by rw [Z.MT];exact D.data.right.g6 _
     obtain ⟨P,hP,hArc⟩:= hOld e he beta B hB (by rw [hBT];exact hSubset hv) (by rw [hBT];exact hSubset hw)
     have hPP: P=D.Ng:= Option.some.inj (hP.symm.trans hActive)
     subst P
     obtain ⟨i,hi,hie⟩:= mem_image.mp hArc
     have hMem:(D.Ng.IG i).2∈Z.right.vertices:= by rw [hie];exact hw
     have hNew:= D.eM Z i (mem_range.mp hi) hMem
     rw [hie] at hNew
     exact ⟨_,rfl,hNew⟩
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma Bb.qU {S: tI G M ell} {x y: Fin N}
   {R: y7 S x y} (A: Bb R) (E: Finset (Fin N ×Fin N))
   (hEndpoints: S.C4 E) (hOld: S.ND.y4 E):
   A.Nj.ND.y4 (insert (x,y) E):= by
 intro e he r B hB hv hw
 rcases mem_insert.mp he with he|he
 · subst e
   obtain ⟨C,hC,hP,hm,hExt,hHeld⟩:= A.EG
   have hX: A.Nf.vertex (2*R.NX.length)=x:=(A.Iz.2 _ le_rfl).trans R.NC
   have hXMem: x∈C.tree.vertices:= by
     have hh:=C.tree.EA A.Nf (C.inside A.Nf hP)
       (A.Nf.mem_support (2*R.NX.length) (by have hp:=A.yY;omega))
     simpa only [hX] using hh
   have hroot:= A.Nj.ND.BE r R.root x ⟨B,hB,hv⟩ ⟨C,hC,hXMem⟩
   subst r
   have hBC: B=C:= Option.some.inj (hB.symm.trans hC)
   subst B
   exact ⟨A.Nf,hP,A.tQ⟩
 · exact A.AA E hEndpoints hOld e he r B hB hv hw
lemma Ll.active {mode: Bool} {x y: Fin N} {E E': Finset (Fin N ×Fin N)}
   {S T: tI G M ell} (h: Ll mode x y E S T E')
   (hEndpoints: S.C4 E) (hOld: S.ND.y4 E): T.ND.y4 E':= by
 cases h with
 | augmentation R hFlag =>
   intro e he r B hB hv hw
   change (if r∈({R.ME,R.L7}:Finset (Fin N)) then none else S.ND.state r)=some B at hB
   split_ifs at hB
   exact hOld e he r B hB hv hw
 | extension hMode R hNo A => exact A.qU E hEndpoints hOld
 | skip hNo hNoExt => exact hOld
inductive Lk (mode: Bool): List (Fin N ×Fin N)→ tI G M ell→
   Finset (Fin N ×Fin N)→ tI G M ell→ Finset (Fin N ×Fin N)→ Prop where
 | nil (S: tI G M ell) (E: Finset (Fin N ×Fin N)): Lk mode [] S E S E
 | cons {x y: Fin N} {es: List (Fin N ×Fin N)} {S U T: tI G M ell}
     {E F H: Finset (Fin N ×Fin N)} (step: Ll mode x y E S U F) (rest: Lk mode es U F T H):
     Lk mode ((x,y)::es) S E T H
lemma M2.wZ {mode: Bool} {es: List (Fin N ×Fin N)} {S T: tI G M ell}
   (h: M2 mode es S T) (E: Finset (Fin N ×Fin N)):∃F,Lk mode es S E T F:= by
 induction h generalizing E with
 | nil => exact ⟨E,Lk.nil _ E⟩
 | cons step rest ih =>
   obtain ⟨F,hF⟩:= step.w0 E
   obtain ⟨H,hH⟩:= ih F
   exact ⟨H,Lk.cons hF hH⟩
lemma Lk.z1 {mode: Bool} {es: List (Fin N ×Fin N)}
   {S T: tI G M ell} {E F: Finset (Fin N ×Fin N)} (h: Lk mode es S E T F)
   (hEndpoints: S.C4 E) (hActive: S.ND.y4 E):
   T.C4 F∧ T.ND.y4 F:= by
 induction h with
 | nil => exact ⟨hEndpoints,hActive⟩
 | cons step rest ih => exact ih (step.LD hEndpoints) (step.active hEndpoints hActive)
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
namespace G8
variable (F: G8 G M)
def M8: Finset (Fin N ×Fin N):= univ.biUnion (fun r=>(F.state r).elim ∅ (fun R=>R.tree.NS))
def J9 (E: Finset (Fin N ×Fin N)): SimpleGraph (Fin N):= M⊔Mv G (F.M8∪E)
lemma Jm (e: Fin N ×Fin N): e∈F.M8↔
   ∃r R,F.state r=some R∧ e∈R.tree.NS:= by
 constructor
 · intro he
   obtain ⟨r,hr,he⟩:= mem_biUnion.mp he
   cases hR:F.state r with
   | none => simp [hR] at he
   | some R => exact ⟨r,R,hR,by simpa only [hR,Option.elim_some] using he⟩
 · rintro ⟨r,R,hR,he⟩
   exact mem_biUnion.mpr ⟨r,mem_univ _,by simpa only [hR,Option.elim_some] using he⟩
lemma AR {r: Fin N} (R: Lp G M r) (hR: F.state r=some R): R.tree.NS⊆F.M8:=
 fun e he=>(F.Jm e).mpr ⟨r,R,hR,he⟩
lemma eI (E: Finset (Fin N ×Fin N)) {r: Fin N}
   (R: Lp G M r) (hR: F.state r=some R): Mv G R.tree.NS≤F.J9 E:= by
 intro u v h
 right
 rcases h.2 with he|he
 · exact ⟨h.1,Or.inl (mem_union_left _ (F.AR R hR he))⟩
 · exact ⟨h.1,Or.inr (mem_union_left _ (F.AR R hR he))⟩
lemma vS {r: Fin N} (R: Lp G M r) (hR: F.state r=some R)
   (u v: Fin N) (hu: u∈R.tree.vertices) (h:(Mv G F.M8).Adj u v): v∈R.tree.vertices:= by
 have hOwners:∃s B,F.state s=some B∧ u∈B.tree.vertices∧ v∈B.tree.vertices:= by
   rcases h.2 with he|he
   · obtain ⟨s,B,hB,he⟩:=(F.Jm (u,v)).mp he
     have hv:=B.tree.Ft u v he
     exact ⟨s,B,hB,hv⟩
   · obtain ⟨s,B,hB,he⟩:=(F.Jm (v,u)).mp he
     have hv:=B.tree.Ft v u he
     exact ⟨s,B,hB,hv.symm⟩
 obtain ⟨s,B,hB,huB,hvB⟩:= hOwners
 have hsr:= F.BE s r u ⟨B,hB,huB⟩ ⟨R,hR,hu⟩
 subst s
 have hBR: B=R:= Option.some.inj (hB.symm.trans hR)
 subst B
 exact hvB
end G8
lemma tI.cK (S: tI G M ell)
   (E: Finset (Fin N ×Fin N)) (hE: S.C4 E) {r: Fin N}
   (R: Lp G M r) (hR: S.ND.state r=some R) (hExt: R.extended=false)
   (u v: Fin N) (hu: u∈R.tree.vertices) (h:(S.ND.J9 E).Adj u v): v∈R.tree.vertices:= by
 rcases h with hM|h
 · exact R.tree.iA S.MG u hu v hM
 · have hAlive: u∉S.Nm:= S.k7 r R hR u hu
   rcases h.2 with he|he
   · rcases mem_union.mp he with he|he
     · exact S.ND.vS R hR u v hu ⟨h.1,Or.inl he⟩
     · exact (S.ND.bS u (hE (u,v) he u (Or.inl rfl) hAlive) R hR hExt hu).elim
   · rcases mem_union.mp he with he|he
     · exact S.ND.vS R hR u v hu ⟨h.1,Or.inr he⟩
     · exact (S.ND.bS u (hE (v,u) he u (Or.inr rfl) hAlive) R hR hExt hu).elim
end Be
end
noncomputable section
namespace Be
variable {V: Type} [DecidableEq V]
def Ba (H: SimpleGraph V) (X: Finset V): Prop:=
 ∀u∈X,∀v∈X,∃p: H.Walk u v,∀w∈p.support,w∈X
def J1 (H: SimpleGraph V) (B: Finset V) (x y: V): Prop:=
 ∀u∈B,∀v,v∉B→ H.Adj u v→ u=x∧ v=y
lemma s7 {H: SimpleGraph V} {B: Finset V} {x y u v: V}
   (hGate: J1 H B x y) (p: H.Walk u v) (hu: u∈B) (hv: v∉B):
   x∈p.support∧ y∈p.support:= by
 induction p with
 | nil => exact (hv hu).elim
 | @cons u z v huz p ih =>
   by_cases hz: z∈B
   · obtain ⟨hx,hy⟩:= ih hz hv
     exact ⟨by simp only [SimpleGraph.Walk.support_cons,List.mem_cons];exact Or.inr hx,
       by simp only [SimpleGraph.Walk.support_cons,List.mem_cons];exact Or.inr hy⟩
   · obtain ⟨hux,hzy⟩:= hGate u hu z hz huz
     constructor
     · simpa only [hux] using (SimpleGraph.Walk.cons huz p).start_mem_support
     · exact List.mem_cons_of_mem u (hzy ▸p.start_mem_support)
lemma x8 {H: SimpleGraph V} {B: Finset V} {x y u v: V}
   (hGate: J1 H B x y) (p: H.Walk u v) (hp: p.IsPath)
   (hu: u∉B) (hv: v∉B):∀w∈p.support,w∉B:= by
 induction p with
 | nil => simpa using hu
 | @cons u z v huz p ih =>
   obtain ⟨hPath,hNot⟩:=(SimpleGraph.Walk.cons_isPath_iff huz p).mp hp
   have hz: z∉B:= by
     intro hz
     have hEq:=(hGate z hz u hu huz.symm).2
     have hY:=(s7 hGate p hz hv).2
     exact hNot (hEq ▸hY)
   intro w hw
   rcases (List.mem_cons.mp hw) with hw|hw
   · rwa [hw]
   · exact ih hPath hz hv w hw
lemma iB {H J: SimpleGraph V} {u v: V} (p: H.Walk u v)
   (D: Finset V) (hSupport:∀w∈p.support,w∈D)
   (hAdj:∀a∈D,∀b∈D,H.Adj a b→ J.Adj a b):
   ∃q: J.Walk u v,q.support=p.support:= by
 have hEdges:∀e∈p.edges,e∈J.edgeSet:= by
   intro e he
   obtain ⟨⟨a,b⟩,hab⟩:= e.exists_rep
   rw [←hab] at he ⊢
   have hA:= p.fst_mem_support_of_mem_edges he
   have hB:= p.snd_mem_support_of_mem_edges he
   exact J.mem_edgeSet.mpr (hAdj a (hSupport a hA) b (hSupport b hB) (H.mem_edgeSet.mp (p.edges_subset_edgeSet he)))
 exact ⟨p.transfer J hEdges,SimpleGraph.Walk.support_transfer p hEdges⟩
lemma sX (J: SimpleGraph V) (B: Finset V) (x y: V)
   (hClosed:∀u∈B,∀v,J.Adj u v→ v∈B) (hx: x∈B) (hy: y∉B):
   J1 (J⊔SimpleGraph.edge x y) B x y:= by
 intro u hu v hv hadj
 rcases hadj with hadj|hadj
 · exact (hv (hClosed u hu v hadj)).elim
 · rcases ((SimpleGraph.edge_adj x y u v).mp hadj).1 with h|h
   · exact h
   · exact (hy (h.1 ▸hu)).elim
lemma cA {J: SimpleGraph V} {B X: Finset V} {x y: V}
   (hClosed:∀u∈B,∀v,J.Adj u v→ v∈B) (hx: x∈B) (hy: y∉B)
   (hX: Ba (J⊔SimpleGraph.edge x y) X): Ba J (X\B):= by
 intro u hu v hv
 obtain ⟨p,hSupport⟩:= hX u (mem_sdiff.mp hu).1 v (mem_sdiff.mp hv).1
 let q:= p.toPath
 have hOutside:= x8 (sX J B x y hClosed hx hy) q.val q.property
   (mem_sdiff.mp hu).2 (mem_sdiff.mp hv).2
 have hSmall:∀w∈q.val.support,w∈X\B:= by
   intro w hw
   exact mem_sdiff.mpr ⟨hSupport w (p.support_toPath_subset_support hw),hOutside w hw⟩
 have hAdj:∀a∈X\B,∀b∈X\B,(J⊔SimpleGraph.edge x y).Adj a b→ J.Adj a b:= by
   intro a ha b hb hadj
   rcases hadj with hadj|hadj
   · exact hadj
   · rcases ((SimpleGraph.edge_adj x y a b).mp hadj).1 with he|he
     · exact ((mem_sdiff.mp ha).2 (he.1 ▸hx)).elim
     · exact ((mem_sdiff.mp hb).2 (he.2 ▸hx)).elim
 obtain ⟨old,hOld⟩:= iB q.val (X\B) hSmall hAdj
 exact ⟨old,by rw [hOld];exact hSmall⟩
end Be
end
noncomputable section
namespace Be
variable {V: Type} [DecidableEq V]
def F2 (E: Finset (V×V)) (X: Finset V): Finset (V×V):= E.filter (fun e=>e.1∈X∧ e.2∈X)
def Fm (J: SimpleGraph V) (E: Finset (V×V)) (A L: ℕ): Prop:=
 ∀X,Ba J X→ X.card≤A+L*(F2 E X).card
lemma Ba.mono {H J: SimpleGraph V} {X: Finset V} (h: Ba H X) (hHJ: H≤J):
   Ba J X:= by
 intro u hu v hv
 obtain ⟨p,hP⟩:= h u hu v hv
 refine ⟨p.map (.ofLE hHJ),?_⟩
 intro w hw
 simpa only [SimpleGraph.Walk.support_map,SimpleGraph.Hom.ofLE_apply,List.map_id] using hP w (by simpa using hw)
lemma Fm.KF {H J: SimpleGraph V} {E: Finset (V×V)} {A L: ℕ}
   (h: Fm J E A L) (hHJ: H≤J): Fm H E A L:=
 fun X hX=>h X (hX.mono hHJ)
lemma Fm.KE {J: SimpleGraph V} {E F: Finset (V×V)} {A L: ℕ}
   (h: Fm J E A L) (hEF: E⊆F): Fm J F A L:= by
 intro X hX
 exact (h X hX).trans (Nat.add_le_add_left (Nat.mul_le_mul_left L (card_le_card (filter_subset_filter _ hEF))) A)
lemma C1 {J: SimpleGraph V} {B: Finset V} {u v: V}
   (hClosed:∀a∈B,∀b,J.Adj a b→ b∈B) (p: J.Walk u v) (hu: u∈B): v∈B:= by
 induction p with
 | nil => exact hu
 | cons hadj p ih => exact ih (hClosed _ hu _ hadj)
lemma Ba.GN {J: SimpleGraph V} {X B: Finset V}
   (h: Ba J X) (hClosed:∀a∈B,∀b,J.Adj a b→ b∈B)
   (hHit:(X∩B).Nonempty): X⊆B:= by
 obtain ⟨u,hu⟩:= hHit
 intro v hv
 obtain ⟨p,hP⟩:= h u (mem_inter.mp hu).1 v hv
 exact C1 hClosed p (mem_inter.mp hu).2
lemma rL {E: Finset (V×V)} {X B: Finset V}
   (hEnds:∀e∈E,e.1∉B∧ e.2∉B): F2 E (X\B)=F2 E X:= by
 ext e
 by_cases he: e∈E
 · obtain ⟨h1,h2⟩:= hEnds e he
   simp only [F2,mem_filter,mem_sdiff,he,true_and,h1,h2,not_false_eq_true,and_true]
 · simp [F2,he]
lemma g1 {J: SimpleGraph V} {E: Finset (V×V)} {A L: ℕ}
   (hOld: Fm J E A L) (B: Finset V) (x y: V)
   (hClosed:∀a∈B,∀b,J.Adj a b→ b∈B) (hx: x∈B) (hy: y∉B)
   (hBase: B.card≤A) (hSmall: B.card≤L) (hEnds:∀e∈E,e.1∉B∧ e.2∉B):
   Fm (J⊔SimpleGraph.edge x y) (insert (x,y) E) A L:= by
 intro X hX
 by_cases hHit:(X∩B).Nonempty
 · by_cases hSub: X⊆B
   · exact (card_le_card hSub).trans (hBase.trans (Nat.le_add_right A _))
   · have hOutside:∃v∈X,v∉B:= by
       by_contra hn
       apply hSub
       intro v hv
       by_contra hvB
       exact hn ⟨v,hv,hvB⟩
     obtain ⟨u,hu⟩:= hHit
     obtain ⟨v,hv,hvB⟩:= hOutside
     obtain ⟨p,hP⟩:= hX u (mem_inter.mp hu).1 v hv
     obtain ⟨hxp,hyp⟩:= s7 (sX J B x y hClosed hx hy) p (mem_inter.mp hu).2 hvB
     have hxX:= hP x hxp
     have hyX:= hP y hyp
     have hFresh:(x,y)∉E:= fun he=>(hEnds (x,y) he).1 hx
     have hCount:(F2 (insert (x,y) E) X).card=(F2 E X).card+1:= by
       have heq: F2 (insert (x,y) E) X=insert (x,y) (F2 E X):= by
         ext e
         simp only [F2,mem_filter,mem_insert]
         constructor
         · rintro ⟨he,hv,hw⟩
           rcases he with he|he
           · exact Or.inl he
           · exact Or.inr ⟨he,hv,hw⟩
         · rintro (he|he)
           · subst e;exact ⟨Or.inl rfl,hxX,hyX⟩
           · exact ⟨Or.inr he.1,he.2⟩
       have hNoInternal:(x,y)∉F2 E X:= fun he=>hFresh (mem_filter.mp he).1
       rw [heq,card_insert_of_notMem hNoInternal]
     have hBound:= hOld (X\B) (cA hClosed hx hy hX)
     rw [rL hEnds] at hBound
     have hCard: X.card≤(X\B).card+B.card:= card_le_card_sdiff_add_card
     rw [hCount]
     nlinarith
 · have hDiff: X\B=X:= by
     apply sdiff_eq_left.mpr
     exact disjoint_iff_inter_eq_empty.mpr (eq_empty_iff_forall_notMem.mpr (fun v hv=>hHit ⟨v,hv⟩))
   have hConn:= cA hClosed hx hy hX
   rw [hDiff] at hConn
   exact (hOld.KE (subset_insert (x,y) E)) X hConn
end Be
end
noncomputable section
namespace Be
variable {V: Type} [DecidableEq V]
lemma g2 {J: SimpleGraph V} {E: Finset (V×V)} {A L: ℕ}
   (hOld: Fm J E A L) (B: Finset V) (x y: V)
   (hClosed:∀a∈B,∀b,J.Adj a b→ b∈B) (hx: x∈B) (hy: y∈B) (hBase: B.card≤A):
   Fm (J⊔SimpleGraph.edge x y) (insert (x,y) E) A L:= by
 have hNewClosed:∀a∈B,∀b,(J⊔SimpleGraph.edge x y).Adj a b→ b∈B:= by
   intro a ha b hadj
   rcases hadj with hadj|hadj
   · exact hClosed a ha b hadj
   · rcases ((SimpleGraph.edge_adj x y a b).mp hadj).1 with he|he
     · exact he.2 ▸hy
     · exact he.2 ▸hx
 intro X hX
 by_cases hHit:(X∩B).Nonempty
 · have hSub:= hX.GN hNewClosed hHit
   exact (card_le_card hSub).trans (hBase.trans (Nat.le_add_right A _))
 · have hOut:∀a∈X,a∉B:= by
     intro a ha hB
     exact hHit ⟨a,mem_inter.mpr ⟨ha,hB⟩⟩
   have hConn: Ba J X:= by
     intro u hu v hv
     obtain ⟨p,hP⟩:= hX u hu v hv
     obtain ⟨q,hQ⟩:= iB p X hP (by
       intro a ha b hb hadj
       rcases hadj with hadj|hadj
       · exact hadj
       · rcases ((SimpleGraph.edge_adj x y a b).mp hadj).1 with he|he
         · exact (hOut a ha (he.1 ▸hx)).elim
         · exact (hOut a ha (he.1 ▸hy)).elim)
     exact ⟨q,by rw [hQ];exact hP⟩
   exact (hOld.KE (subset_insert (x,y) E)) X hConn
lemma g0 {J: SimpleGraph V} {E: Finset (V×V)} {A L: ℕ}
   (hOld: Fm J E A L) (B: Finset V) (x y: V)
   (hClosed:∀a∈B,∀b,J.Adj a b→ b∈B) (hx: x∈B)
   (hBase: B.card≤A) (hSmall: B.card≤L) (hEnds:∀e∈E,e.1∉B∧ e.2∉B):
   Fm (J⊔SimpleGraph.edge x y) (insert (x,y) E) A L:= by
 by_cases hy: y∈B
 · exact g2 hOld B x y hClosed hx hy hBase
 · exact g1 hOld B x y hClosed hx hy hBase hSmall hEnds
end Be
end
noncomputable section
namespace Be.G8
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
def Ns (F: G8 G M) (H: SimpleGraph (Fin N)): Prop:=
 ∀r R,F.state r=some R→∀u v,(u,v)∈R.tree.NS→ H.Adj u v
lemma zN (F K: G8 G M) (H: SimpleGraph (Fin N))
   {a: Fin N} (A: Lp G M a) (hEq: K.state=Function.update F.state a (some A))
   (hOld: F.Ns H) (hA:∀u v,(u,v)∈A.tree.NS→ H.Adj u v): K.Ns H:= by
 intro r R hR u v he
 rw [hEq] at hR
 by_cases hr: r=a
 · subst r
   rw [Function.update_self] at hR
   cases Option.some.inj hR
   exact hA u v he
 · rw [Function.update_of_ne hr] at hR
   exact hOld r R hR u v he
lemma zO (F K: G8 G M) (H: SimpleGraph (Fin N))
   {a b: Fin N} (hab: a≠b) (A: Lp G M a) (B: Lp G M b)
   (hEq: K.state=F.E2 A B) (hOld: F.Ns H)
   (hA:∀u v,(u,v)∈A.tree.NS→ H.Adj u v)
   (hB:∀u v,(u,v)∈B.tree.NS→ H.Adj u v): K.Ns H:= by
 intro r R hR u v he
 rw [hEq] at hR
 by_cases hra: r=a
 · subst r
   rw [F.CZ hab] at hR
   cases Option.some.inj hR
   exact hA u v he
 · by_cases hrb: r=b
   · subst r
     rw [F.E3] at hR
     cases Option.some.inj hR
     exact hB u v he
   · rw [F.C0 A B r hra hrb] at hR
     exact hOld r R hR u v he
lemma Fy (F: G8 G M) (E: Finset (Fin N ×Fin N)) (H: SimpleGraph (Fin N))
   (hM: M≤H) (hOld: F.Ns H) (hE:∀e∈E,G.Adj e.1 e.2→ H.Adj e.1 e.2): F.J9 E≤H:= by
 intro u v h
 rcases h with hMuv|h
 · exact hM hMuv
 · rcases h.2 with he|he
   · rcases mem_union.mp he with he|he
     · obtain ⟨r,R,hR,he⟩:=(F.Jm (u,v)).mp he
       exact hOld r R hR u v he
     · exact hE (u,v) he h.1
   · rcases mem_union.mp he with he|he
     · obtain ⟨r,R,hR,he⟩:=(F.Jm (v,u)).mp he
       exact (hOld r R hR v u he).symm
     · exact (hE (v,u) he h.1.symm).symm
end Be.G8
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma G6.B9 {alpha beta: Fin N} (D: G6 G M alpha beta)
   (H: SimpleGraph (Fin N)) (hL:∀u v,(u,v)∈D.left.NS→ H.Adj u v)
   (hR:∀u v,(u,v)∈D.right.NS→ H.Adj u v)
   (hBridge: H.Adj (D.NX.vertex (2*D.NX.length)) D.target.1):
   ∀u v,(u,v)∈D.KC→ H.Adj u v:= by
 intro u v he
 rcases mem_union.mp he with he|he
 · rcases mem_union.mp he with he|he
   · exact hL u v he
   · exact hR u v he
 · simp only [mem_insert,mem_singleton,Prod.mk.injEq] at he
   rcases he with he|he
   · rw [he.1,he.2];exact hBridge
   · rw [he.1,he.2];exact hBridge.symm
lemma Bb.Fu {S: tI G M ell} {x y: Fin N}
   {R: y7 S x y} (A: Bb R) (H: SimpleGraph (Fin N))
   (hM: M≤H) (hOld: S.ND.Ns H) (hBridge: H.Adj x y): A.Nj.ND.Ns H:= by
 cases A with
 | single hOwner =>
   apply G8.zN S.ND _ H _ rfl hOld
   apply Bi.r7
   intro u v he
   change (u,v)∈R.state.tree.NS∪{(R.NX.vertex (2*R.NX.length),y),(y,R.NX.vertex (2*R.NX.length)),(y,R.NW)} at he
   rcases mem_union.mp he with he|he
   · exact hOld R.root R.state R.present u v he
   · simp only [mem_insert,mem_singleton,Prod.mk.injEq] at he
     rcases he with he|he|he
     · rw [he.1,he.2,R.NC];exact hBridge
     · rw [he.1,he.2,R.NC];exact hBridge.symm
     · rw [he.1,he.2];exact hM R.matched
 | inactive D B hB hAT hBT hSt hTarget hInactive =>
   have hMem:= D.B9 H
     (fun u v he=>hOld R.root R.state R.present u v (by rwa [hAT]))
     (fun u v he=>hOld _ B hB u v (by rwa [hBT])) (by rw [hSt,hTarget,R.NC];exact hBridge)
   apply G8.zO S.ND _ H D.distinct _ _ rfl hOld
   · exact D.JM.dS D.KC D.HW D.En H hMem
   · exact D.remaining.dS D.KC D.HW
       ((D.right.pU _).trans D.AO) H hMem
 | active D B hB hAT hBT hSt hTarget hActive =>
   have hMem:= D.data.B9 H
     (fun u v he=>hOld R.root R.state R.present u v (by rwa [hAT]))
     (fun u v he=>hOld _ B hB u v (by rwa [hBT])) (by rw [hSt,hTarget,R.NC];exact hBridge)
   let Z:= Classical.choice D.transfer
   apply G8.zO S.ND _ H D.data.distinct _ _ rfl hOld
   · exact Z.left.dS D.data.KC D.data.HW Z.Jl H hMem
   · exact Z.right.dS D.data.KC D.data.HW Z.Is H hMem
lemma Bb.zU {S: tI G M ell} {x y: Fin N}
   {R: y7 S x y} (A: Bb R) (E: Finset (Fin N ×Fin N)):
   A.Nj.ND.J9 (insert (x,y) E)≤S.ND.J9 E⊔SimpleGraph.edge x y:= by
 let H:= S.ND.J9 E⊔SimpleGraph.edge x y
 have hM: M≤H:= fun u v h=>Or.inl (Or.inl h)
 have hOld: S.ND.Ns H:= by
   intro r B hB u v he
   exact Or.inl ((S.ND.eI E B hB) ⟨B.tree.valid u v he,Or.inl he⟩)
 have hBridge: H.Adj x y:= Or.inr ((SimpleGraph.edge_adj x y x y).mpr ⟨Or.inl ⟨rfl,rfl⟩,G.ne_of_adj (S.MF R.IY)⟩)
 apply G8.Fy _ _ H hM (A.Fu H hM hOld hBridge)
 intro e he hG
 rcases mem_insert.mp he with he|he
 · subst e;exact hBridge
 · exact Or.inl (Or.inr ⟨hG,Or.inl (mem_union_right _ he)⟩)
lemma tI.bW (S: tI G M ell) {x y: Fin N}
   (R: qF S x y) (E: Finset (Fin N ×Fin N)):
   (S.sE R).ND.J9 E≤S.ND.J9 E:= by
 apply G8.Fy _ _ _ (fun _ _ h=>Or.inl h)
 · intro r B hB u v he
   change (if r∈({R.ME,R.L7}:Finset (Fin N)) then none else S.ND.state r)=some B at hB
   split_ifs at hB
   exact S.ND.eI E B hB ⟨B.tree.valid u v he,Or.inl he⟩
 · intro e he hG
   exact Or.inr ⟨hG,Or.inl (mem_union_right _ he)⟩
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
lemma v9.s8 {r: Fin N} (P: v9 G M r)
   (i: ℕ) (hi: i≤2*P.length):
   ∃p: G.Walk (P.vertex 0) (P.vertex i),∀v∈p.support,v∈P.support:= by
 induction i with
 | zero =>
   refine ⟨.nil,?_⟩
   intro v hv
   have he: v=P.vertex 0:= by simpa using hv
   rw [he];exact P.mem_support 0 (by omega)
 | succ i ih =>
   obtain ⟨p,hP⟩:= ih (by omega)
   have hEdge:= P.Mu i (by omega)
   refine ⟨p.append hEdge.toWalk,?_⟩
   intro v hv
   rcases (SimpleGraph.Walk.mem_support_append_iff p hEdge.toWalk).mp hv with hv|hv
   · exact hP v hv
   · have he: v=P.vertex i∨ v=P.vertex (i+1):= by simpa using hv
     rcases he with he|he
     · rw [he];exact P.mem_support i (by omega)
     · rw [he];exact P.mem_support (i+1) hi
lemma Bi.fY {r: Fin N} (S: Bi G M r)
   (H: SimpleGraph (Fin N)) (hH:∀u v,(u,v)∈S.NS→ H.Adj u v): Ba H S.vertices:= by
 have hRootWalk:∀v∈S.vertices,∃p: H.Walk r v,∀w∈p.support,w∈S.vertices:= by
   intro v hv
   obtain ⟨P,hP,hvP⟩:= S.GZ v hv
   obtain ⟨i,hi,hiv⟩:= mem_image.mp hvP
   have hi': i≤2*P.length:= by have hh:=mem_range.mp hi;omega
   let Q:= P.Nq H (fun j hj=>hH _ _ (hP j hj))
   obtain ⟨p,hSupport⟩:= Q.s8 i hi'
   have hWalk:∃p: H.Walk (Q.vertex 0) (Q.vertex i),∀w∈p.support,w∈S.vertices:=
     ⟨p,fun w hw=>S.EA P hP (hSupport w hw)⟩
   change ∃p: H.Walk (P.vertex 0) (P.vertex i),∀w∈p.support,w∈S.vertices at hWalk
   rw [P.first,hiv] at hWalk
   exact hWalk
 intro u hu v hv
 obtain ⟨left,hLeft⟩:= hRootWalk u hu
 obtain ⟨right,hRight⟩:= hRootWalk v hv
 refine ⟨left.reverse.append right,?_⟩
 intro w hw
 rcases (SimpleGraph.Walk.mem_support_append_iff left.reverse right).mp hw with hw|hw
 · exact hLeft w (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hw)
 · exact hRight w hw
lemma G8.jI {ell: ℕ} (S: tI G M ell)
   (E: Finset (Fin N ×Fin N)) {r: Fin N} (R: Lp G M r) (hR: S.ND.state r=some R):
   Ba (S.ND.J9 E) R.tree.vertices:=
 R.tree.fY _ (fun u v he=>S.ND.eI E R hR ⟨R.tree.valid u v he,Or.inl he⟩)
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
namespace G8
variable (F: G8 G M) {s t: ℕ} (P: tE G t)
   (hOwner:∀v,F.owner (P.leader v)=F.owner v)
def BB (v: Fin N): Fin N:=(F.owner v).getD (P.leader v)
include hOwner in
lemma mL (v: Fin N): F.owner (F.BB P v)=F.owner v:= by
 cases hV: F.owner v with
 | none => simpa [BB,hV] using hOwner v
 | some r =>
   obtain ⟨R,hR,hVR⟩:=(F.KP r v).mp hV
   simpa [BB,hV] using F.KO r R hR
include hOwner in
lemma mK (v: Fin N):
   F.BB P (F.BB P v)=F.BB P v:= by
 have hO:=F.mL P hOwner v
 cases hV: F.owner v with
 | none =>
   simp only [BB,hV,Option.getD_none] at hO ⊢
   rw [hO]
   exact P.fixed v
 | some r =>
   simp only [BB,hV,Option.getD_some] at hO ⊢
   rw [hO]
   rfl
lemma f8 (r v: Fin N) (hV: F.Mm r v): F.BB P v=r:= by
 unfold BB
 rw [(F.KP r v).mpr hV]
 rfl
include hOwner in
lemma dW (u v: Fin N) (hEq: F.BB P u=F.BB P v):
   F.owner u=F.owner v:= by
 rw [←F.mL P hOwner u,←F.mL P hOwner v,hEq]
include hOwner in
lemma eX (u v: Fin N) (hEq: F.BB P u=F.BB P v):
   (Mc G (fun w=>(F.BB P w).val)).Reachable u v:= by
 have hOV:=F.dW P hOwner u v hEq
 cases hOU: F.owner u with
 | some r =>
   have hOV': F.owner v=some r:=hOV.symm.trans hOU
   obtain ⟨A,hA,hUA⟩:=(F.KP r u).mp hOU
   obtain ⟨B,hB,hVB⟩:=(F.KP r v).mp hOV'
   have hAB: A=B:=Option.some.inj (hA.symm.trans hB)
   rw [←hAB] at hVB
   obtain ⟨p,hSupport⟩:=A.tree.fY G A.tree.valid u hUA v hVB
   obtain ⟨q,hq⟩:=iB p A.tree.vertices hSupport
     (J:=Mc G (fun w=>(F.BB P w).val)) (by
       intro a ha b hb hG
       exact ⟨hG,congrArg Fin.val ((F.f8 P r a ⟨A,hA,ha⟩).trans
         (F.f8 P r b ⟨A,hA,hb⟩).symm)⟩)
   exact ⟨q⟩
 | none =>
   have hOV': F.owner v=none:=hOV.symm.trans hOU
   have hPV: P.leader u=P.leader v:=by simpa [BB,hOU,hOV'] using hEq
   obtain ⟨p⟩:=P.connected u v hPV
   have hMono: Mc G (fun w=>(P.leader w).val)≤
       Mc G (fun w=>(F.BB P w).val):= by
     intro a b h
     have hPAB: P.leader a=P.leader b:=Fin.ext h.2
     have hOwners: F.owner a=F.owner b:=by rw [←hOwner a,←hOwner b,hPAB]
     refine ⟨h.1,?_⟩
     change ((F.owner a).getD (P.leader a)).val=((F.owner b).getD (P.leader b)).val
     rw [hOwners,hPAB]
   exact ⟨p.mapLe hMono⟩
include hOwner in
lemma mM (hSize:∀r R,F.state r=some R→ R.tree.vertices.card≤ s)
   (hT: t≤ s) (v: Fin N):
   (univ.filter (fun w=>F.BB P w=F.BB P v)).card≤ s:= by
 cases hOV: F.owner v with
 | none =>
   apply (card_le_card (show univ.filter (fun w=>F.BB P w=F.BB P v) ⊆
     univ.filter (fun w=>P.leader w=P.leader v) from ?_)).trans ((P.small v).trans hT)
   intro w hw
   have hEq:=(mem_filter.mp hw).2
   have hOW: F.owner w=none:=(F.dW P hOwner w v hEq).trans hOV
   exact mem_filter.mpr ⟨mem_univ _,by simpa [BB,hOW,hOV] using hEq⟩
 | some r =>
   obtain ⟨R,hR,hVR⟩:=(F.KP r v).mp hOV
   apply (card_le_card (show univ.filter (fun w=>F.BB P w=F.BB P v) ⊆R.tree.vertices from ?_)).trans (hSize r R hR)
   intro w hw
   have hOW: F.owner w=some r:=(F.dW P hOwner w v (mem_filter.mp hw).2).trans hOV
   obtain ⟨Q,hQ,hWQ⟩:=(F.KP r w).mp hOW
   have hQR: Q=R:=Option.some.inj (hQ.symm.trans hR)
   exact hQR ▸hWQ
def tT (hSize:∀r R,F.state r=some R→ R.tree.vertices.card≤ s)
   (hT: t≤ s): tE G s where
 leader:=F.BB P
 fixed:=F.mK P hOwner
 connected:=F.eX P hOwner
 small:=F.mM P hOwner hSize hT
end G8
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
namespace G8
lemma t7 (F: G8 G M) (hM: Matching G M)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (v: Fin N):
   F.owner ((tE.Hv G M hM ids hi).leader v)=F.owner v:= by
 rw [tE.q7]
 unfold representative
 split_ifs
 · rfl
 · rcases x7 ids hi M v with hFix|hAdj
   · rw [hFix]
   · exact (F.sB hM v _ hAdj).symm
end G8
namespace tI
variable {ell s: ℕ} (S: tI G M ell)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (hSize:∀r R,S.ND.state r=some R→ R.tree.vertices.card≤ s) (hS: 2≤ s)
def tT: tE G s:=
 S.ND.tT (tE.Hv G M S.MG ids hi)
   (S.ND.t7 S.MG ids hi) hSize hS
end tI
end Be
end
noncomputable section
namespace Be.tF
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)} (A: tF)
   (S: tI G M ell) (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (out: Fin N→ Option ℕ) (hOut: ReportsMatching G ids out M)
lemma pS (hRep: A.Represents S ids hi out hOut):
   ∃(r: Fin N) (R: Lp G M r),S.ND.state r=some R∧ ids r=A.leader∧
     R.tree.vertices.image ids=A.members:= by
 obtain ⟨hAuth,hState⟩:=hRep
 let E:=A.history.embedding hAuth hi hOut A.KB
 refine ⟨E.toFun A.root,A.state.Nd E,hState,A.history.yA hAuth A.root,?_⟩
 change (A.state.Nd E).tree.vertices.image ids=A.state.tree.vertices.image A.history.identity
 rw [A.state.Aj E,image_image]
 apply congrArg (fun f=>A.state.tree.vertices.image f)
 funext i
 exact A.history.yA hAuth i
lemma sP (hRep: A.Represents S ids hi out hOut) (v: Fin N)
   (hV: ids v∈A.members):∃r,ids r=A.leader∧ S.ND.Mm r v:= by
 obtain ⟨r,R,hR,hID,hMembers⟩:=A.pS S ids hi out hOut hRep
 rw [←hMembers] at hV
 obtain ⟨u,hu,hUV⟩:=mem_image.mp hV
 exact ⟨r,hID,R,hR,hi hUV ▸hu⟩
end Be.tF
end
noncomputable section
namespace Be.tI
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ} (S: tI G M ell)
def Et: SimpleGraph (Fin N):=
 exchange M (Ld G S.found (fun P=> P.Nm)) (Ld G S.found (fun P=> P.added))
lemma Eu: Matching G S.Et∧ matchingSize S.Et= matchingSize M+S.found.card:=
 nJ S.found id S.DQ S.MG
lemma Cq: matchingSize M≤ matchingSize S.Et:= by
 rw [S.Eu.2]
 omega
lemma x3: matchingSize S.Et≤ optimum G:=
 qJ.gQ G S.Et S.Eu.1
end Be.tI
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
structure Fi (S: tI G M ell) (ids: Fin N→ ℕ)
   (hi: Function.Injective ids) (out: Fin N→ Option ℕ) (hOut: ReportsMatching G ids out M)
   (data: Fin N→ Ln): Prop where
 neighbors:∀v,(data v).neighbors=neighborIDs G ids v
 Jf:∀v,(data v).Jf=out v
 labels:∀u v,(data u).labels (ids v)=S.labels (u,v)
 Nm:∀v,(data v).Nm=true↔ v∈S.Nm
 NV:∀u v,S.NV.Adj u v↔ G.Adj u v∧(data u).Nm=false∧(data v).Nm=false∧
   ids v∉(data u).ignored∧ ids u∉(data v).ignored
 Jr:∀v A,(data v).L8=some A→
   A.Represents S ids hi out hOut∧ ids v∈A.members
 El:∀r R,S.ND.state r=some R→
   ∃A,∀v∈R.tree.vertices,(data v).L8=some A
 output: ReportsMatching G ids (fun v=>if (data v).Nm then (data v).Md else (data v).Jf) S.Et
namespace Fi
variable {S: tI G M ell} {ids: Fin N→ ℕ} {hi: Function.Injective ids}
   {out: Fin N→ Option ℕ} {hOut: ReportsMatching G ids out M}
   {data: Fin N→ Ln} (h: Fi S ids hi out hOut data)
include h
lemma As (v: Fin N) (hV:(data v).L8=none): S.ND.owner v=none:= by
 apply (S.ND.KN v).mpr
 rintro r ⟨R,hR,hVR⟩
 obtain ⟨A,hA⟩:=h.El r R hR
 have hh:=hA v hVR
 rw [hV] at hh
 cases hh
lemma Gr {s: ℕ} (hSize:∀r R,S.ND.state r=some R→ R.tree.vertices.card≤ s)
   (hS: 2≤ s) (v: Fin N):
   (data v).leader (ids v)=ids ((S.tT ids hi hSize hS).leader v):= by
 change (data v).leader (ids v)=ids (S.ND.BB
   (tE.Hv G M S.MG ids hi) v)
 cases hModel:(data v).L8 with
 | none =>
   have hOwner:=h.As v hModel
   have hNamed:=tE.t6 G M ids hi out hOut v
   simpa [Ln.leader,hModel,G8.BB,hOwner,h.Jf v]
     using hNamed
 | some A =>
   obtain ⟨hRep,hMem⟩:=h.Jr v A hModel
   obtain ⟨r,hID,hContains⟩:=A.sP S ids hi out hOut hRep v hMem
   have hOwner:=(S.ND.KP r v).mpr hContains
   simpa [Ln.leader,hModel,G8.BB,hOwner] using hID.symm
end Fi
end Be
end
noncomputable section
namespace Be.tF
def AV (j: ℕ) (neighbors: Finset ℕ): y6:={(j,(neighbors,none))}
lemma nZ (j: ℕ) (neighbors: Finset ℕ):(AV j neighbors).keys={j}:= by
 simp [AV,y6.keys]
lemma dF (j: ℕ) (neighbors: Finset ℕ):(AV j neighbors).JS:= by
 intro a ha b hb hEq
 exact (mem_singleton.mp ha).trans (mem_singleton.mp hb).symm
lemma dG (j: ℕ) (neighbors: Finset ℕ):(AV j neighbors).JX:= by
 intro a ha b hMate
 rw [nZ] at ha
 have hAJ:=mem_singleton.mp ha
 subst a
 have hLook: lookup (AV j neighbors) j=some (neighbors,none):=by
   apply Ea (AV j neighbors) (fun (_: Unit)=>j)
     (fun _=>(neighbors,(none: Option ℕ))) (fun _ _ _=>Subsingleton.elim _ _)
   · intro z hz;exact ⟨(),mem_singleton.mp hz⟩
   · exact ()
   · exact mem_singleton_self _
 simp [y6.NW,hLook] at hMate
def Jg (j: ℕ) (neighbors: Finset ℕ): tF:= by
 let D:=AV j neighbors
 have hCard: D.keys.card=1:=by rw [nZ,card_singleton]
 let r: Fin D.keys.card:=⟨0,by omega⟩
 have hFree:∀v,¬D.MG.Adj r v:=by
   intro v hEdge
   have hEq: r=v:=Fin.ext (by have hv:=v.isLt;have hr:=r.isLt;omega)
   exact hEdge.ne hEq
 let R:=Lp.initial D.graph D.MG r hFree
 refine ⟨D,dF j neighbors,dG j neighbors,r,R,?_⟩
 intro Q i hi
 have hEdge:=(Q.Mu i hi).2
 change (Q.vertex i,Q.vertex (i+1))∈(∅: Finset (Fin D.keys.card ×Fin D.keys.card))∨
   (Q.vertex (i+1),Q.vertex i)∈(∅: Finset (Fin D.keys.card ×Fin D.keys.card)) at hEdge
 simp at hEdge
lemma uD (j: ℕ) (neighbors: Finset ℕ):(Jg j neighbors).leader=j:= by
 have hMem:=(AV j neighbors).Hy (Jg j neighbors).root
 rw [nZ] at hMem
 exact mem_singleton.mp hMem
lemma rJ (j: ℕ) (neighbors: Finset ℕ):(Jg j neighbors).members={j}:= by
 change ({(Jg j neighbors).root}: Finset _).image (Jg j neighbors).history.identity={j}
 rw [image_singleton]
 exact congrArg singleton (uD j neighbors)
end Be.tF
end
noncomputable section
namespace Be
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)}
namespace v9
variable (E: wF G M H K) {r: Fin N} (Q: v9 G M r)
lemma o9 (u v: Fin N) (i: ℕ):
   (Q.Nd E).He (E.toFun u) (E.toFun v) i=E.toFun (Q.He u v i):= by
 unfold He
 dsimp only [Nd]
 by_cases h: i≤ 2*Q.length<;> by_cases h': i=2*Q.length+1<;> simp [h,h']
end v9
namespace Lp
variable (E: wF G M H K) {r: Fin N} (R: Lp G M r)
lemma m8:(R.Nd E).tree.vertices.card=R.tree.vertices.card:= by
 rw [R.Aj E]
 exact card_image_of_injective _ E.injective
lemma rS (limit: ℕ):(R.IX limit).Nd E=(R.Nd E).IX limit:= by
 apply Lp.Kd
 · rfl
 · rfl
 · change (R.NU&& decide (limit≤ R.tree.vertices.card))=
     ((R.Nd E).NU&& decide (limit≤(R.Nd E).tree.vertices.card))
   rw [R.m8 E]
   rfl
 · rfl
 · rfl
lemma c2 (limit: ℕ):
   (R.rC limit).Nd E=(R.Nd E).rC limit:= by
 apply Lp.Kd
 · rfl
 · rfl
 · change (R.NU|| decide (limit≤ R.tree.vertices.card))=
     ((R.Nd E).NU|| decide (limit≤(R.Nd E).tree.vertices.card))
   rw [R.m8 E]
   rfl
 · rfl
 · rfl
lemma xE: R.backtrack.Nd E=(R.Nd E).backtrack:= by
 apply Lp.Kd
 · rfl
 · cases hA: R.active with
   | none => simp [Lp.Nd,backtrack,hA]
   | some Q =>
     by_cases hLen: 0< Q.length
     · simp [Lp.Nd,backtrack,hA,v9.Nd,v9.take,hLen]
     · simp [Lp.Nd,backtrack,hA,v9.Nd,v9.take,hLen]
 · rfl
 · rfl
 · rfl
lemma gL: R.zS.Nd E=(R.Nd E).zS:= by
 unfold zS
 change (if R.NU|| R.modified then R else R.backtrack).Nd E=
   if R.NU|| R.modified then R.Nd E else (R.Nd E).backtrack
 split_ifs
 · rfl
 · exact R.xE E
end Lp
end Be
end
noncomputable section
namespace Be
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)}
namespace Lp
lemma B1 (E: wF G M H K) (r: Fin N) (hFree:∀v,¬M.Adj r v):
   (initial G M r hFree).Nd E=initial H K (E.toFun r) (E.free_map r hFree):= by
 apply Kd
 · apply Bi.FJ
   change (∅: Finset (Fin N ×Fin N)).image E.pairMap=∅
   simp
 · rfl
 · rfl
 · rfl
 · rfl
end Lp
namespace tF
variable {ell: ℕ} (G M: SimpleGraph (Fin N)) (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (out: Fin N→ Option ℕ) (hOut: ReportsMatching G ids out M)
lemma kN (v: Fin N) (hV: out v=none):
   (Jg (ids v) (neighborIDs G ids v)).Represents
     (tI.initial G M hOut.1 ell) ids hi out hOut:= by
 let A:=Jg (ids v) (neighborIDs G ids v)
 have hAuth: A.history.Li G ids out:=by
   intro z hz
   have hZ: z=(ids v,(neighborIDs G ids v,none)):=mem_singleton.mp hz
   exact ⟨v,by rw [hV];exact hZ⟩
 refine ⟨hAuth,?_⟩
 let E:=A.history.embedding hAuth hi hOut A.KB
 change (G8.initial G M).state (E.toFun A.root)=some (A.state.Nd E)
 have hFree:∀w,¬A.history.MG.Adj A.root w:=A.state.tree.L9
 have hInitial: A.state=Lp.initial A.history.graph A.history.MG A.root hFree:=rfl
 rw [hInitial,Lp.B1 E A.root hFree]
 change (if h:∀w,¬M.Adj (E.toFun A.root) w then
   some (Lp.initial G M (E.toFun A.root) h) else none)=_
 rw [dif_pos (E.free_map A.root hFree)]
end tF
end Be
end
noncomputable section
namespace Be
namespace Ln
def K8 (ell: ℕ) (j: ℕ) (neighbors: Finset ℕ) (NW: Option ℕ): Ln where
 neighbors:=neighbors
 Jf:=NW
 labels _:=ell+1
 ignored:=∅
 Nm:=false
 Md:=NW
 L8:=if NW=none then some (tF.Jg j neighbors) else none
end Ln
namespace tI
variable {N: ℕ} (G M: SimpleGraph (Fin N)) (hM: Matching G M) (ell: ℕ)
lemma kO:(initial G M hM ell).Et=M:= by
 ext u v
 simp [Et,initial,exchange,Ld,zD.GB]
end tI
lemma gI {N ell: ℕ} (G M: SimpleGraph (Fin N))
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (out: Fin N→ Option ℕ)
   (hOut: ReportsMatching G ids out M):
   Fi (tI.initial G M hOut.1 ell) ids hi out hOut
     (fun v=>Ln.K8 ell (ids v) (neighborIDs G ids v) (out v)):= by
 refine ⟨fun _=>rfl,fun _=>rfl,fun _ _=>rfl,?_,?_,?_,?_,?_⟩
 · intro v;simp [Ln.K8,tI.initial]
 · intro u v;simp [Ln.K8,tI.initial]
 · intro v A hA
   change (if out v=none then some (tF.Jg (ids v) (neighborIDs G ids v)) else none)=some A at hA
   split_ifs at hA with hNone
   cases Option.some.inj hA
   exact ⟨tF.kN G M ids hi out hOut v hNone,
     by rw [tF.rJ];exact mem_singleton_self _⟩
 · intro r R hR
   change (if h:∀w,¬M.Adj r w then some (Lp.initial G M r h) else none)=some R at hR
   split_ifs at hR with hFree
   cases Option.some.inj hR
   refine ⟨tF.Jg (ids r) (neighborIDs G ids r),?_⟩
   intro v hv
   have hVR: v=r:=mem_singleton.mp hv
   subst v
   have hNone: out r=none:=(hOut.2 r).1.mpr hFree
   simp [Ln.K8,hNone]
 · simpa only [Ln.K8,Bool.false_eq_true,if_false,tI.kO] using hOut
end Be
end
noncomputable section
namespace Be.IO
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)} {S: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (D: IO) (h: Fi S ids hi out hOut data)
   (hD:∀z∈D,∃v,z=(ids v,data v))
include h hD
lemma w7: D.history.Li G ids out:= by
 intro z hz
 rcases mem_union.mp hz with hz|hz
 · obtain ⟨⟨j,node⟩,hNode,hEq⟩:=mem_image.mp hz
   obtain ⟨v,hV⟩:=hD (j,node) hNode
   obtain ⟨rfl,rfl⟩:=Prod.mk.inj hV
   refine ⟨v,?_⟩
   rw [←hEq]
   exact Prod.ext rfl (Prod.ext (h.neighbors v) (h.Jf v))
 · obtain ⟨⟨j,node⟩,hNode,hz⟩:=mem_biUnion.mp hz
   obtain ⟨v,hV⟩:=hD (j,node) hNode
   obtain ⟨rfl,rfl⟩:=Prod.mk.inj hV
   change z∈(data v).L8.elim ∅ (fun A=>A.history) at hz
   cases hA:(data v).L8 with
   | none => simp [hA] at hz
   | some A =>
     have hRep:=(h.Jr v A hA).1
     obtain ⟨hAuth,hState⟩:=hRep
     exact hAuth z (by simpa only [hA,Option.elim_some] using hz)
lemma Jw (v: Fin N) (hKey: ids v∈D.keys): D.node (ids v)=data v:= by
 have hMem:(ids v,data v)∈D:=by
   obtain ⟨⟨j,node⟩,hZ,hID⟩:=mem_image.mp hKey
   obtain ⟨u,hU⟩:=hD (j,node) hZ
   have hUV: u=v:=hi ((congrArg Prod.fst hU).symm.trans hID)
   cases hUV
   exact hU ▸hZ
 have hLookup:=Ea D ids data hi hD v hMem
 exact congrArg (fun z=>z.getD default) hLookup
lemma uB (hPair:∀v,ids v∈D.keys→∀w,M.Adj v w→ ids w∈D.keys):
   D.history.JX:= by
 have hAuth:=D.w7 h hD
 intro j hj k hMate
 have hKeys: D.history.keys=D.GM.keys∪
     y6.keys (D.biUnion (fun z=>z.2.L8.elim ∅ (fun A=>A.history))):=image_union _ _
 rw [hKeys] at hj
 rcases mem_union.mp hj with hj|hj
 · rw [D.vZ] at hj
   obtain ⟨v,hV⟩:=D.history.Fv hAuth j (D.rP hj)
   have hKey: ids v∈D.keys:=by rw [hV];exact hj
   have hM: out v=some k:=by
     rw [←hV,D.history.Dj hi hAuth v (D.rP hKey)] at hMate
     exact hMate
   obtain ⟨w,hVW,hID⟩:=((hOut.2 v).2 k).mp hM
   exact D.rP (by rw [←hID];exact hPair v hKey w hVW)
 · obtain ⟨z,hZ,hJ⟩:=mem_image.mp hj
   obtain ⟨⟨a,node⟩,hNode,hZ⟩:=mem_biUnion.mp hZ
   obtain ⟨v,hV⟩:=hD (a,node) hNode
   obtain ⟨rfl,rfl⟩:=Prod.mk.inj hV
   cases hA:(data v).L8 with
   | none => simp [hA] at hZ
   | some A =>
     obtain ⟨hAuthA,hState⟩:=(h.Jr v A hA).1
     have hZA: z∈A.history:=by simpa only [hA,Option.elim_some] using hZ
     have hJA: j∈A.history.keys:=mem_image.mpr ⟨z,hZA,hJ⟩
     exact A.history.Bx D.history hi hAuthA hAuth
       (D.pF _ _ hNode A hA) A.KB j hJA k hMate
end Be.IO
end
noncomputable section
namespace Be.G8
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)}
   (E: wF G M H K)
lemma DF (F T: G8 G M) (h: F.state=T.state): F=T:= by
 cases F
 cases T
 cases h
 rfl
def Mr (F: G8 G M) (T: G8 H K): Prop:=
 ∀r R,F.state r=some R→ T.state (E.toFun r)=some (R.Nd E)
lemma Mr.update_one {F F': G8 G M} {T T': G8 H K}
   (hMap: Mr E F T) {r: Fin N} (A: Lp G M r)
   (B: Lp H K (E.toFun r)) (hAB: A.Nd E=B)
   (hF: F'.state=Function.update F.state r (some A))
   (hT: T'.state=Function.update T.state (E.toFun r) (some B)): Mr E F' T':= by
 intro s R hR
 rw [hF] at hR
 rw [hT]
 by_cases hs: s=r
 · subst s
   rw [Function.update_self] at hR ⊢
   cases Option.some.inj hR
   exact congrArg some hAB.symm
 · rw [Function.update_of_ne hs] at hR
   rw [Function.update_of_ne (fun h=>hs (E.injective h))]
   exact hMap s R hR
lemma Mr.Le {F F': G8 G M} {T T': G8 H K}
   (hMap: Mr E F T) {r s: Fin N} (hrs: r≠s)
   (A: Lp G M r) (B: Lp G M s)
   (A': Lp H K (E.toFun r)) (B': Lp H K (E.toFun s))
   (hA: A.Nd E=A') (hB: B.Nd E=B')
   (hF: F'.state=F.E2 A B) (hT: T'.state=T.E2 A' B'): Mr E F' T':= by
 intro v R hR
 rw [hF] at hR
 rw [hT]
 by_cases hvr: v=r
 · subst v
   rw [F.CZ hrs] at hR
   rw [T.CZ (fun h=>hrs (E.injective h))]
   cases Option.some.inj hR
   exact congrArg some hA.symm
 · by_cases hvs: v=s
   · subst v
     rw [F.E3] at hR
     rw [T.E3]
     cases Option.some.inj hR
     exact congrArg some hB.symm
   · rw [F.C0 A B v hvr hvs] at hR
     rw [T.C0 A' B' (E.toFun v) (fun h=>hvr (E.injective h)) (fun h=>hvs (E.injective h))]
     exact hMap v R hR
end Be.G8
end
noncomputable section
namespace Be
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)}
abbrev J0 (G M: SimpleGraph (Fin N)):=(r: Fin N) ×Lp G M r
namespace J0
def Valid (D: Finset (J0 G M)): Prop:=
 (∀a∈D,∀b∈D,a.1=b.1→ a=b)∧
 ∀a∈D,∀b∈D,a.1≠b.1→ Disjoint a.2.tree.vertices b.2.tree.vertices
def ND (D: Finset (J0 G M)) (hD: Valid D): G8 G M where
 state r:=if h:∃R: Lp G M r,⟨r,R⟩∈D then some h.choose else none
 disjoint:=by
   intro r s hRS A B hA hB
   split_ifs at hA with hRA
   split_ifs at hB with hSB
   cases Option.some.inj hA
   cases Option.some.inj hB
   exact hD.2 ⟨r,hRA.choose⟩ hRA.choose_spec ⟨s,hSB.choose⟩ hSB.choose_spec hRS
lemma BN (D: Finset (J0 G M)) (hD: Valid D) (r: Fin N) (R: Lp G M r):
   (ND D hD).state r=some R↔⟨r,R⟩∈D:= by
 change (if h:∃Q: Lp G M r,⟨r,Q⟩∈D then some h.choose else none)=some R↔ _
 split_ifs with h
 · constructor
   · intro hR;cases Option.some.inj hR;exact h.choose_spec
   · intro hR
     have hEq:(⟨r,h.choose⟩: J0 G M)=⟨r,R⟩:=hD.1 _ h.choose_spec _ hR rfl
     have hState: h.choose=R:=by cases hEq;rfl
     exact congrArg some hState
 · constructor
   · intro hR;cases hR
   · intro hR;exact (h ⟨R,hR⟩).elim
lemma v6 (E: wF G M H K) (T: G8 H K)
   (D: Finset (J0 G M))
   (hD:∀a∈D,T.state (E.toFun a.1)=some (a.2.Nd E)): Valid D:= by
 constructor
 · rintro ⟨r,A⟩ hA ⟨s,B⟩ hB hRS
   change r=s at hRS
   subst s
   have hMap: A.Nd E=B.Nd E:=Option.some.inj ((hD ⟨r,A⟩ hA).symm.trans (hD ⟨r,B⟩ hB))
   have hTree: A.tree=B.tree:=by
     apply Bi.FJ
     have hArcs:=congrArg (fun (R: Lp H K (E.toFun r))=>R.tree.NS) hMap
     ext a
     rw [←E.Jn A.tree.NS a.1 a.2,←E.Jn B.tree.NS a.1 a.2]
     exact congrArg (fun C=>(E.toFun a.1,E.toFun a.2)∈C) hArcs|>.to_iff
   have hActive: A.active=B.active:=by
     have hAct:=congrArg Lp.active hMap
     change A.active.map (fun Q=>Q.Nd E)=B.active.map (fun Q=>Q.Nd E) at hAct
     apply Option.map_injective _ hAct
     intro Q R hQR
     apply v9.Kd
     · exact congrArg (fun (Q: v9 H K (E.toFun r))=>Q.length) hQR
     · funext i
       exact E.injective (congrArg (fun Q=>Q.vertex i) hQR)
   have hEq: A=B:=Lp.Kd A B hTree hActive
     (congrArg (fun (R: Lp H K (E.toFun r))=>R.NU) hMap) (congrArg (fun (R: Lp H K (E.toFun r))=>R.modified) hMap) (congrArg (fun (R: Lp H K (E.toFun r))=>R.extended) hMap)
   cases hEq
   rfl
 · intro a ha b hb hNe
   have hDis:=T.disjoint _ _ (fun h=>hNe (E.injective h)) _ _ (hD a ha) (hD b hb)
   rw [a.2.Aj E,b.2.Aj E] at hDis
   apply disjoint_left.mpr
   intro v hv hw
   exact disjoint_left.mp hDis (mem_image.mpr ⟨v,hv,rfl⟩) (mem_image.mpr ⟨v,hw,rfl⟩)
lemma Ja (E: wF G M H K) (T: G8 H K)
   (D: Finset (J0 G M)) (hD: Valid D)
   (hMap:∀a∈D,T.state (E.toFun a.1)=some (a.2.Nd E)):
   G8.Mr E (ND D hD) T:= by
 intro r R hR
 exact hMap ⟨r,R⟩ ((BN D hD r R).mp hR)
end J0
end Be
end
noncomputable section
namespace Be.IO
def K3 (D: IO) (A: tF): Option (J0 D.history.graph D.history.MG):=
 if h: Nonempty (y9 A.history D.history) then
   some ⟨h.some.map.toFun A.root,A.state.Nd h.some.map⟩ else none
def JF (D: IO): Finset (J0 D.history.graph D.history.MG):=
 D.biUnion (fun z=>(z.2.L8.bind (D.K3)).toFinset)
lemma sU (D: IO) (A: tF)
   (R: J0 D.history.graph D.history.MG) (hR: D.K3 A=some R):
   R.2.tree.qK:= by
 unfold K3 at hR
 split_ifs at hR with h
 cases Option.some.inj hR
 exact A.state.tree.Ag h.some.map A.complete
lemma vQ (D: IO) (A: tF)
   (R: J0 D.history.graph D.history.MG) (hR: D.K3 A=some R):
   R.2.tree.vertices.image D.history.identity=A.members:= by
 unfold K3 at hR
 split_ifs at hR with h
 cases Option.some.inj hR
 rw [A.state.Aj h.some.map,image_image]
 apply congrArg (fun f=>A.state.tree.vertices.image f)
 funext i
 exact h.some.identity i
lemma vR (D: IO) (R: J0 D.history.graph D.history.MG)
   (hR: R∈D.JF):
   ∃z∈D,∃A,z.2.L8=some A∧ D.K3 A=some R:= by
 obtain ⟨z,hZ,hR⟩:=mem_biUnion.mp hR
 obtain ⟨A,hA,hRecord⟩:=Option.bind_eq_some_iff.mp (Option.mem_toFinset.mp hR)
 exact ⟨z,hZ,A,hA,hRecord⟩
lemma pZ (D: IO) (R: J0 D.history.graph D.history.MG)
   (hR: R∈D.JF): R.2.tree.qK:= by
 obtain ⟨z,hZ,hR⟩:=mem_biUnion.mp hR
 have hOpt: z.2.L8.bind D.K3=some R:=Option.mem_toFinset.mp hR
 obtain ⟨A,hA,hRecord⟩:=Option.bind_eq_some_iff.mp hOpt
 exact D.sU A R hRecord
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)} {S: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (D: IO) (h: Fi S ids hi out hOut data)
   (hD:∀z∈D,∃v,z=(ids v,data v))
   (hClosed: D.history.JX)
include h hD hClosed in
lemma yN (v: Fin N) (hV:(ids v,data v)∈D)
   (A: tF) (hA:(data v).L8=some A):
   ∃R,D.K3 A=some R:= by
 obtain ⟨hAuthA,hState⟩:=(h.Jr v A hA).1
 have hAuthD:=D.w7 h hD
 have hSubset:=A.history.LL D.history (D.pF _ _ hV A hA)
 have hEmbedding:=A.history.iY D.history hi hOut hAuthA hAuthD A.KB hClosed hSubset
 unfold K3
 rw [dif_pos hEmbedding]
 exact ⟨_,rfl⟩
lemma CG (v: Fin N) (hV:(ids v,data v)∈D)
   (A: tF) (hA:(data v).L8=some A)
   (R: J0 D.history.graph D.history.MG) (hR: D.K3 A=some R):
   let E:=D.history.embedding (D.w7 h hD) hi hOut hClosed
   S.ND.state (E.toFun R.1)=some (R.2.Nd E):= by
 obtain ⟨hAuthA,hState⟩:=(h.Jr v A hA).1
 unfold K3 at hR
 split_ifs at hR with hEmbedding
 cases Option.some.inj hR
 dsimp only
 let F:=hEmbedding.some
 let E:=D.history.embedding (D.w7 h hD) hi hOut hClosed
 change S.ND.state (E.toFun (F.map.toFun A.root))=some ((A.state.Nd F.map).Nd E)
 rw [A.state.HM F.map E]
 change S.ND.state ((F.map.comp E).toFun A.root)=some (A.state.Nd (F.map.comp E))
 rw [F.DD hi hOut hAuthA (D.w7 h hD) A.KB hClosed]
 exact hState
lemma AQ (R: J0 D.history.graph D.history.MG) (hR: R∈D.JF):
   let E:=D.history.embedding (D.w7 h hD) hi hOut hClosed
   S.ND.state (E.toFun R.1)=some (R.2.Nd E):= by
 obtain ⟨z,hZ,hR⟩:=mem_biUnion.mp hR
 obtain ⟨v,hV⟩:=hD z hZ
 subst z
 have hOpt:(data v).L8.bind D.K3=some R:=Option.mem_toFinset.mp hR
 obtain ⟨A,hA,hRecord⟩:=Option.bind_eq_some_iff.mp hOpt
 exact D.CG h hD hClosed v hZ A hA R hRecord
end Be.IO
end
noncomputable section
namespace Be.IO
structure C5 (D: IO) (ell: ℕ)
   (S: tI D.history.graph D.history.MG ell): Prop where
 ND:∀r R,S.ND.state r=some R↔(⟨r,R⟩: J0 D.history.graph D.history.MG)∈D.JF
 labels: S.labels=D.labels ell
 Nm: S.Nm=univ\D.alive
 NV: S.NV=D.NV
 found: S.found=∅
def view (D: IO) (ell: ℕ): Option (tI D.history.graph D.history.MG ell):=
 if h:∃S,C5 D ell S then some h.choose else none
lemma Mk (D: IO) (ell: ℕ) (h:∃S,C5 D ell S):
   ∃S,D.view ell=some S∧ C5 D ell S:= by
 unfold view
 rw [dif_pos h]
 exact ⟨h.choose,rfl,h.choose_spec⟩
lemma Lf (D: IO) (ell: ℕ)
   (S: tI D.history.graph D.history.MG ell) (hS: D.view ell=some S):
   C5 D ell S:= by
 unfold view at hS
 split_ifs at hS with h
 cases Option.some.inj hS
 exact h.choose_spec
lemma FC (D: IO) (ell: ℕ)
   (S T: tI D.history.graph D.history.MG ell)
   (hS: C5 D ell S) (hT: C5 D ell T): S=T:= by
 have hForest: S.ND=T.ND:=by
   have hState: S.ND.state=T.ND.state:=by
     funext r
     cases hR: S.ND.state r with
     | none =>
       cases hQ: T.ND.state r with
       | none => rfl
       | some R =>
         have hPresent:=(hS.ND r R).mpr ((hT.ND r R).mp hQ)
         rw [hR] at hPresent
         cases hPresent
     | some R => exact ((hT.ND r R).mpr ((hS.ND r R).mp hR)).symm
   exact G8.DF S.ND T.ND hState
 have hLabels:=hS.labels.trans hT.labels.symm
 have hRemoved:=hS.Nm.trans hT.Nm.symm
 have hLive:=hS.NV.trans hT.NV.symm
 have hFound:=hS.found.trans hT.found.symm
 cases S
 cases T
 cases hForest
 cases hLabels
 cases hRemoved
 cases hLive
 cases hFound
 rfl
end Be.IO
end
noncomputable section
namespace Be.IO
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)} {S: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (D: IO) (h: Fi S ids hi out hOut data)
   (hD:∀z∈D,∃v,z=(ids v,data v)) (hClosed: D.history.JX)
include hi hD in
lemma KQ (v: Fin N) (hKey: ids v∈D.keys):(ids v,data v)∈D:= by
 obtain ⟨z,hZ,hID⟩:=mem_image.mp hKey
 obtain ⟨u,hU⟩:=hD z hZ
 have hUV: u=v:=hi ((congrArg Prod.fst hU).symm.trans hID)
 subst u
 exact hU ▸hZ
include h hD hClosed
lemma Gj (u: Fin D.history.keys.card) (hKey: D.history.identity u∈D.keys):
   D.node (D.history.identity u)=data (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun u):= by
 have hID: ids (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun u)=D.history.identity u:=D.history.yA (D.w7 h hD) u
 rw [←hID]
 exact D.Jw h hD (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun u) (hID.symm ▸hKey)
lemma Ls (u: Fin D.history.keys.card):
   u∈D.alive↔ D.history.identity u∈D.keys∧((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun u∉S.Nm:= by
 simp only [alive,mem_filter,mem_univ,true_and]
 constructor
 · rintro ⟨hKey,hNode⟩
   rw [D.Gj h hD hClosed u hKey] at hNode
   refine ⟨hKey,?_⟩
   intro hRemoved
   have hTrue:=(h.Nm _).mpr hRemoved
   rw [hNode] at hTrue
   cases hTrue
 · rintro ⟨hKey,hNot⟩
   refine ⟨hKey,?_⟩
   rw [D.Gj h hD hClosed u hKey]
   cases hBool:(data (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun u)).Nm with
   | false => rfl
   | true => exact (hNot ((h.Nm _).mp hBool)).elim
lemma BV (a: Fin D.history.keys.card ×Fin D.history.keys.card) (hA: a.1∈D.alive):
   D.labels ell a=S.labels (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun a.1,((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun a.2):= by
 have hKey:=((D.Ls h hD hClosed a.1).mp hA).1
 rw [labels,if_pos hKey,D.Gj h hD hClosed a.1 hKey]
 rw [←D.history.yA (D.w7 h hD) a.2]
 exact h.labels _ _
lemma F6 (u v: Fin D.history.keys.card):
   D.NV.Adj u v↔ u∈D.alive∧ v∈D.alive∧ S.NV.Adj (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun u) (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun v):= by
 constructor
 · rintro ⟨hG,hu,hv,hUV,hVU⟩
   have hKU:=((D.Ls h hD hClosed u).mp hu).1
   have hKV:=((D.Ls h hD hClosed v).mp hv).1
   rw [D.Gj h hD hClosed u hKU] at hUV
   rw [D.Gj h hD hClosed v hKV] at hVU
   refine ⟨hu,hv,(h.NV _ _).mpr ⟨(((D.history.embedding (D.w7 h hD) hi hOut hClosed)).LH _ _).mpr hG,?_,?_,?_,?_⟩⟩
   · have hh:=((D.Ls h hD hClosed u).mp hu).2
     cases hb:(data (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun u)).Nm with
     | false => rfl
     | true => exact (hh ((h.Nm _).mp hb)).elim
   · have hh:=((D.Ls h hD hClosed v).mp hv).2
     cases hb:(data (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun v)).Nm with
     | false => rfl
     | true => exact (hh ((h.Nm _).mp hb)).elim
   · have hID: ids (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun v)=D.history.identity v:=D.history.yA (D.w7 h hD) v
     rw [hID]
     exact hUV
   · have hID: ids (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun u)=D.history.identity u:=D.history.yA (D.w7 h hD) u
     rw [hID]
     exact hVU
 · rintro ⟨hu,hv,hLive⟩
   obtain ⟨hG,hU,hV,hUV,hVU⟩:=(h.NV _ _).mp hLive
   have hKU:=((D.Ls h hD hClosed u).mp hu).1
   have hKV:=((D.Ls h hD hClosed v).mp hv).1
   refine ⟨(((D.history.embedding (D.w7 h hD) hi hOut hClosed)).LH _ _).mp hG,hu,hv,?_,?_⟩
   · rw [D.Gj h hD hClosed u hKU,←D.history.yA (D.w7 h hD) v]
     exact hUV
   · rw [D.Gj h hD hClosed v hKV,←D.history.yA (D.w7 h hD) u]
     exact hVU
end Be.IO
end
noncomputable section
namespace Be.IO
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)} {S: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (D: IO) (h: Fi S ids hi out hOut data)
   (hD:∀z∈D,∃v,z=(ids v,data v)) (hClosed: D.history.JX)
   (hPair:∀v,ids v∈D.keys→∀w,M.Adj v w→ ids w∈D.keys)
   (hWhole:∀v,ids v∈D.keys→∀r R,S.ND.state r=some R→ v∈R.tree.vertices→
     ∀w∈R.tree.vertices,ids w∈D.keys)
include h hD hClosed
include hPair in
lemma l1 (u: Fin D.history.keys.card) (hU: u∈D.alive)
   (v: Fin D.history.keys.card) (hM: D.history.MG.Adj u v): v∈D.alive:= by
 obtain ⟨hKey,hNot⟩:=(D.Ls h hD hClosed u).mp hU
 have hIDU: ids (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun u)=D.history.identity u:=D.history.yA (D.w7 h hD) u
 have hIDV: ids (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun v)=D.history.identity v:=D.history.yA (D.w7 h hD) v
 have hPhys: M.Adj (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun u) (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun v):=(((D.history.embedding (D.w7 h hD) hi hOut hClosed)).HS u v).mpr hM
 apply (D.Ls h hD hClosed v).mpr
 refine ⟨?_,?_⟩
 · rw [←hIDV]
   exact hPair _ (hIDU.symm ▸hKey) _ hPhys
 · exact fun hRemoved=>hNot (S.EL _ hRemoved _ hPhys.symm)
include hWhole in
lemma nP (R: J0 D.history.graph D.history.MG) (hR: R∈D.JF):
   R.2.tree.vertices⊆D.alive:= by
 obtain ⟨z,hZ,A,hA,hRecord⟩:=D.vR R hR
 obtain ⟨v,hV⟩:=hD z hZ
 subst z
 obtain ⟨hRep,hMember⟩:=h.Jr v A hA
 have hMembers:=D.vQ A R hRecord
 rw [←hMembers] at hMember
 obtain ⟨a,ha,hAV⟩:=mem_image.mp hMember
 have hAV':((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun a=v:=hi ((D.history.yA (D.w7 h hD) a).trans hAV)
 have hState:=D.AQ h hD hClosed R hR
 have hSource: v∈(R.2.Nd (D.history.embedding (D.w7 h hD) hi hOut hClosed)).tree.vertices:=by
   rw [R.2.Aj (D.history.embedding (D.w7 h hD) hi hOut hClosed)]
   exact mem_image.mpr ⟨a,ha,hAV'⟩
 have hKeyV: ids v∈D.keys:=mem_image.mpr ⟨(ids v,data v),hZ,rfl⟩
 intro b hb
 have hPhysical:((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun b∈(R.2.Nd (D.history.embedding (D.w7 h hD) hi hOut hClosed)).tree.vertices:=by
   rw [R.2.Aj (D.history.embedding (D.w7 h hD) hi hOut hClosed)];exact mem_image.mpr ⟨b,hb,rfl⟩
 apply (D.Ls h hD hClosed b).mpr
 refine ⟨?_,S.k7 _ _ hState _ hPhysical⟩
 rw [←D.history.yA (D.w7 h hD) b]
 exact hWhole v hKeyV _ _ hState hSource _ hPhysical
lemma Gv (v: Fin D.history.keys.card) (hV: v∈D.alive)
   (r: Fin N) (R: Lp G M r) (hR: S.ND.state r=some R)
   (hVR:((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun v∈R.tree.vertices):
   ∃Q∈D.JF,((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun Q.1=r:= by
 have hKey:=((D.Ls h hD hClosed v).mp hV).1
 have hID: ids (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun v)=D.history.identity v:=D.history.yA (D.w7 h hD) v
 have hPhysKey: ids (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun v)∈D.keys:=hID.symm ▸hKey
 have hMem:=D.KQ (hi:=hi) hD (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun v) hPhysKey
 obtain ⟨A,hA⟩:=h.El r R hR
 have hModel:=hA (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun v) hVR
 obtain ⟨Q,hQ⟩:=D.yN h hD hClosed (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun v) hMem A hModel
 have hMember: Q∈D.JF:=by
   apply mem_biUnion.mpr
   refine ⟨(ids (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun v),data (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun v)),hMem,?_⟩
   apply Option.mem_toFinset.mpr
   simp [hModel,hQ]
 have hOwnID:=(h.Jr (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun v) A hModel).2
 rw [←D.vQ A Q hQ] at hOwnID
 obtain ⟨a,ha,hIDa⟩:=mem_image.mp hOwnID
 have hAV:((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun a=((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun v:=hi ((D.history.yA (D.w7 h hD) a).trans hIDa)
 have hSource:((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun v∈(Q.2.Nd (D.history.embedding (D.w7 h hD) hi hOut hClosed)).tree.vertices:=by
   rw [Q.2.Aj (D.history.embedding (D.w7 h hD) hi hOut hClosed)]
   exact mem_image.mpr ⟨a,ha,hAV⟩
 exact ⟨Q,hMember,S.ND.BE _ _ (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun v)
   ⟨Q.2.Nd (D.history.embedding (D.w7 h hD) hi hOut hClosed),D.AQ h hD hClosed Q hMember,hSource⟩ ⟨R,hR,hVR⟩⟩
lemma BW (a: Fin D.history.keys.card ×Fin D.history.keys.card): 1≤ D.labels ell a:= by
 unfold labels
 split_ifs with hKey
 · rw [D.Gj h hD hClosed a.1 hKey]
   rw [←D.history.yA (D.w7 h hD) a.2,h.labels]
   exact S.positive _
 · omega
lemma HH (a: Fin D.history.keys.card ×Fin D.history.keys.card): D.labels ell a≤ ell+1:= by
 unfold labels
 split_ifs with hKey
 · rw [D.Gj h hD hClosed a.1 hKey]
   rw [←D.history.yA (D.w7 h hD) a.2,h.labels]
   exact S.upper _
 · rfl
end Be.IO
end
noncomputable section
namespace Be.IO
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)} {S: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (D: IO) (h: Fi S ids hi out hOut data)
   (hD:∀z∈D,∃v,z=(ids v,data v)) (hClosed: D.history.JX)
   (hPair:∀v,ids v∈D.keys→∀w,M.Adj v w→ ids w∈D.keys)
   (hWhole:∀v,ids v∈D.keys→∀r R,S.ND.state r=some R→ v∈R.tree.vertices→
     ∀w∈R.tree.vertices,ids w∈D.keys)
include h hD hClosed hPair hWhole in
lemma cX:
   ∃U: tI D.history.graph D.history.MG ell,
     C5 D ell U∧ Db (D.history.embedding (D.w7 h hD) hi hOut hClosed) U S:= by
 have hMap:=D.AQ h hD hClosed
 have hValid: J0.Valid D.JF:=J0.v6 (D.history.embedding (D.w7 h hD) hi hOut hClosed) S.ND D.JF hMap
 let F:=J0.ND D.JF hValid
 have hPresent:∀r R,F.state r=some R→ S.ND.state (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun r)=some (R.Nd (D.history.embedding (D.w7 h hD) hi hOut hClosed)):=
   J0.Ja (D.history.embedding (D.w7 h hD) hi hOut hClosed) S.ND D.JF hValid hMap
 have hVertices:∀r R,F.state r=some R→ R.tree.vertices⊆D.alive:=by
   intro r R hR
   exact D.nP h hD hClosed hWhole ⟨r,R⟩ ((J0.BN D.JF hValid r R).mp hR)
 have hCover:∀v,v∈D.alive→∀r R,S.ND.state r=some R→((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun v∈R.tree.vertices→
     ∃s U,F.state s=some U∧((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun s=r:=by
   intro v hv r R hR hVR
   obtain ⟨Q,hQ,hEq⟩:=D.Gv h hD hClosed v hv r R hR hVR
   exact ⟨Q.1,Q.2,(J0.BN D.JF hValid Q.1 Q.2).mpr hQ,hEq⟩
 have hComp: F.qK:=by
   intro r R hR
   exact D.pZ ⟨r,R⟩ ((J0.BN D.JF hValid r R).mp hR)
 let U:=Dv (D.history.embedding (D.w7 h hD) hi hOut hClosed) S D.alive F (D.labels ell) D.NV D.history.Eg
   (D.l1 h hD hClosed hPair)
   (fun v hv=>((D.Ls h hD hClosed v).mp hv).2)
   hPresent hVertices hCover (D.F6 h hD hClosed) (D.BV h hD hClosed)
   (D.BW h hD hClosed) (D.HH h hD hClosed) hComp
 refine ⟨U,?_,?_⟩
 · exact ⟨J0.BN D.JF hValid,rfl,rfl,rfl,rfl⟩
 · exact gA (D.history.embedding (D.w7 h hD) hi hOut hClosed) S D.alive F (D.labels ell) D.NV D.history.Eg
     (D.l1 h hD hClosed hPair)
     (fun v hv=>((D.Ls h hD hClosed v).mp hv).2)
     hPresent hVertices hCover (D.F6 h hD hClosed) (D.BV h hD hClosed)
     (D.BW h hD hClosed) (D.HH h hD hClosed) hComp
include h hD hClosed hPair hWhole in
lemma n6:
   ∃U: tI D.history.graph D.history.MG ell,
     D.view ell=some U∧ Db (D.history.embedding (D.w7 h hD) hi hOut hClosed) U S:= by
 obtain ⟨U,hCompatible,hEmbed⟩:=D.cX h hD hClosed hPair hWhole
 obtain ⟨V,hView,hV⟩:=D.Mk ell ⟨U,hCompatible⟩
 have hUV: U=V:=D.FC ell U V hCompatible hV
 exact ⟨V,hView,hUV ▸hEmbed⟩
end Be.IO
end
noncomputable section
namespace Fd
variable {I O: Type}
def MN (f: ℕ→ I→ Multiset (ℕ ×I)→ O): Deterministic Unit I O where
 program:={
   State:= ℕ ×I ×Multiset (ℕ ×I)
   Msg:= ℕ ×I
   rounds:= fun _=> 1
   init:= fun _ id inp _=>(id,inp,0)
   send:= fun st=>(st.1,st.2.1)
   step:= fun st msgs=>(st.1,st.2.1,msgs)
   out:= fun st=> f st.1 st.2.1 st.2.2}
 tape_independent:= by intros; rfl
lemma Cn (f: ℕ→ I→ Multiset (ℕ ×I)→ O) {V: Type} [Fintype V]
   (H: SimpleGraph V) (ids: V→ ℕ) (inp: V→ I) (v: V):
   (MN f).program.output H () ids inp (fun _ _=> false) v=
     f (ids v) (inp v) ((H.neighborFinset v).val.map (fun w=>(ids w,inp w))):= by
 have hn: univ.filter (H.Adj v)= H.neighborFinset v:= by ext w; simp
 change f (ids v) (inp v) ((univ.filter (H.Adj v)).val.map (fun w=>(ids w,inp w)))= _
 rw [hn]
end Fd
end
noncomputable section
namespace Be
abbrev Nw (I: Type):= Finset (ℕ ×I)
abbrev E9 (I: Type):= ℕ→ ℕ→ ℕ→ ℕ→ Nw I→ Nw I→ Prop
def allowed {I: Type} (rule: E9 I) (u v a b: ℕ) (A B: Nw I): Prop:=
 rule u v a b A B∨ rule v u b a B A
lemma Hd {I: Type} (rule: E9 I) (u v a b: ℕ) (A B: Nw I):
   allowed rule u v a b A B↔ allowed rule v u b a B A:= or_comm
def Dn {I: Type} (rule: E9 I) (id: ℕ) (info: ℕ ×Nw I)
   (messages: Multiset (ℕ ×ℕ ×Nw I)): Finset ℕ:=
 (messages.toFinset.filter (fun m=> allowed rule id m.1 info.1 m.2.1 info.2 m.2.2)).image (fun m=> m.2.1)
namespace tE
variable {N: ℕ} {G: SimpleGraph (Fin N)} {s: ℕ} {I: Type} (P: tE G s)
   (ids: Fin N→ ℕ) (inp: Fin N→ I)
def NI (v: Fin N): Nw I:=
 (univ.filter (fun w=> P.leader w= P.leader v)).image (fun w=>(ids w,inp w))
lemma L3 (u v: Fin N) (he: P.leader u= P.leader v): P.NI ids inp u= P.NI ids inp v:= by
 unfold NI
 rw [he]
def Lx (rule: E9 I) (u v: Fin N): Prop:=
 allowed rule (ids u) (ids v) (ids (P.leader u)) (ids (P.leader v)) (P.NI ids inp u) (P.NI ids inp v)
lemma Dr (rule: E9 I): Symmetric (P.Lx ids inp rule):= by
 intro u v h
 exact (Hd rule _ _ _ _ _ _).mp h
def BZ (rule: E9 I) (v: Fin N): Finset ℕ:=
 ((G.neighborFinset v).filter (P.Lx ids inp rule v)).image (fun w=> ids (P.leader w))
lemma j5 (rule: E9 I) (v: Fin N):
   Dn rule (ids v) (ids (P.leader v),P.NI ids inp v)
     ((G.neighborFinset v).val.map (fun w=>(ids w,ids (P.leader w),P.NI ids inp w)))= P.BZ ids inp rule v:= by
 ext j
 constructor
 · intro hj
   obtain ⟨m,hm,heq⟩:= mem_image.mp hj
   obtain ⟨hm,hallowed⟩:= mem_filter.mp hm
   obtain ⟨w,hw,hmw⟩:= Multiset.mem_map.mp (Multiset.mem_toFinset.mp hm)
   subst m
   exact mem_image.mpr ⟨w,mem_filter.mpr ⟨hw,hallowed⟩,heq⟩
 · intro hj
   obtain ⟨w,hw,heq⟩:= mem_image.mp hj
   exact mem_image.mpr ⟨(ids w,ids (P.leader w),P.NI ids inp w),
     mem_filter.mpr ⟨Multiset.mem_toFinset.mpr (Multiset.mem_map.mpr ⟨w,(mem_filter.mp hw).1,rfl⟩),(mem_filter.mp hw).2⟩,heq⟩
def EQ (rule: E9 I) (v: Fin N): Finset ℕ:=
 if ids v= ids (P.leader v) then
   ((univ.filter (fun w=> P.leader w= P.leader v)).biUnion (P.BZ ids inp rule)).filter (fun j=> j≠ ids v)
 else ∅
lemma lH (hi: Function.Injective ids) (rule: E9 I) (v: Fin N):
   P.EQ ids inp rule v= neighborIDs (P.Lv (P.Lx ids inp rule) (P.Dr ids inp rule)) ids v:= by
 by_cases hv: P.leader v= v
 · have hvid: ids v= ids (P.leader v):= by rw [hv]
   rw [EQ,if_pos hvid]
   ext j
   constructor
   · intro hj
     obtain ⟨hjn,hjne⟩:= mem_filter.mp hj
     obtain ⟨u,hu,huj⟩:= mem_biUnion.mp hjn
     obtain ⟨w,hw,hwj⟩:= mem_image.mp huj
     have hleaderu: P.leader u= v:=(mem_filter.mp hu).2.trans hv
     have hne: v≠ P.leader w:= by intro h;apply hjne;rw [←hwj,h]
     have hadj:(P.Lv (P.Lx ids inp rule) (P.Dr ids inp rule)).Adj v (P.leader w):=
       ⟨hv,P.fixed w,hne,u,w,hleaderu,rfl,(G.mem_neighborFinset u w).mp (mem_filter.mp hw).1,(mem_filter.mp hw).2⟩
     exact mem_image.mpr ⟨P.leader w,(SimpleGraph.mem_neighborFinset _ v (P.leader w)).mpr hadj,hwj⟩
   · intro hj
     obtain ⟨b,hb,rfl⟩:= mem_image.mp hj
     obtain ⟨_,_,hne,u,w,hu,hw,hG,hcand⟩:=(SimpleGraph.mem_neighborFinset _ v b).mp hb
     apply mem_filter.mpr
     constructor
     · refine mem_biUnion.mpr ⟨u,mem_filter.mpr ⟨mem_univ _,hu.trans hv.symm⟩,?_⟩
       exact mem_image.mpr ⟨w,mem_filter.mpr ⟨(G.mem_neighborFinset u w).mpr hG,hcand⟩,congrArg ids hw⟩
     · intro heq
       exact hne (hi heq).symm
 · have hvid:¬ids v= ids (P.leader v):= by intro h;exact hv (hi h).symm
   rw [EQ,if_neg hvid]
   symm
   apply eq_empty_iff_forall_notMem.mpr
   intro j hj
   obtain ⟨w,hw,_⟩:= mem_image.mp hj
   exact hv ((SimpleGraph.mem_neighborFinset _ v w).mp hw).1
end tE
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma tI.iV (S: tI G M ell)
   {r: Fin N} (R: Lp G M r) (hR: S.ND.state r=some R)
   (u v: Fin N) (hu: u∈R.tree.vertices) (h:(S.ND.J9 ∅).Adj u v): v∈R.tree.vertices:= by
 rcases h with hM|h
 · exact R.tree.iA S.MG u hu v hM
 · have hMemory:(Mv G S.ND.M8).Adj u v:= by simpa only [union_empty] using h
   exact S.ND.vS R hR u v hu hMemory
lemma tI.cN (S: tI G M ell)
   (u v: Fin N) (hNo:∀r R,S.ND.state r=some R→ u∉R.tree.vertices)
   (h:(S.ND.J9 ∅).Adj u v): M.Adj u v:= by
 rcases h with hM|h
 · exact hM
 · simp only [union_empty] at h
   rcases h.2 with he|he
   · obtain ⟨r,R,hR,he⟩:=(S.ND.Jm (u,v)).mp he
     exact (hNo r R hR (R.tree.Ft u v he).1).elim
   · obtain ⟨r,R,hR,he⟩:=(S.ND.Jm (v,u)).mp he
     exact (hNo r R hR (R.tree.Ft v u he).2).elim
lemma tI.eN (S: tI G M ell)
   {u v: Fin N} (p:(S.ND.J9 ∅).Walk u v)
   (hNo:∀r R,S.ND.state r=some R→ u∉R.tree.vertices): u=v∨ M.Adj u v:= by
 induction p with
 | nil => exact Or.inl rfl
 | @cons u z v huz p ih =>
   have hM:= S.cN u z hNo huz
   have hNoZ:∀r R,S.ND.state r=some R→ z∉R.tree.vertices:= by
     intro r R hR hz
     exact hNo r R hR (R.tree.iA S.MG z hz u hM.symm)
   rcases ih hNoZ with hEq|hAdj
   · exact Or.inr (hEq ▸hM)
   · exact Or.inl (qJ.gP G M S.MG z u v hM.symm hAdj)
lemma tI.kP (S: tI G M ell) (A L: ℕ)
   (hA: 2≤A) (hSize:∀r R,S.ND.state r=some R→ R.tree.vertices.card≤A):
   Fm (S.ND.J9 ∅) ∅ A L:= by
 intro X hX
 have hGoal: X.card≤A:= by
   by_cases hNonempty: X.Nonempty
   · obtain ⟨u,hu⟩:= hNonempty
     by_cases hOwned:∃r R,S.ND.state r=some R∧ u∈R.tree.vertices
     · obtain ⟨r,R,hR,huR⟩:= hOwned
       have hSub:= hX.GN (fun a ha b hadj=>S.iV R hR a b ha hadj)
         ⟨u,mem_inter.mpr ⟨hu,huR⟩⟩
       exact (card_le_card hSub).trans (hSize r R hR)
     · have hNo:∀r R,S.ND.state r=some R→ u∉R.tree.vertices:=
         fun r R hR hm=>hOwned ⟨r,R,hR,hm⟩
       have hEvery:∀v∈X,u=v∨ M.Adj u v:= by
         intro v hv
         obtain ⟨p,hP⟩:= hX u hu v hv
         exact S.eN p hNo
       by_cases hMate:∃w,M.Adj u w
       · obtain ⟨w,hw⟩:= hMate
         have hSub: X⊆{u,w}:= by
           intro v hv
           rcases hEvery v hv with he|he
           · exact mem_insert.mpr (Or.inl he.symm)
           · have hvw:=qJ.gP G M S.MG u v w he hw
             exact mem_insert.mpr (Or.inr (mem_singleton.mpr hvw))
         have hCard:({u,w}:Finset (Fin N)).card≤2:= by
           exact (card_insert_le _ _).trans (by rw [card_singleton])
         exact (card_le_card hSub).trans (hCard.trans hA)
       · have hSub: X⊆{u}:= by
           intro v hv
           rcases hEvery v hv with he|he
           · exact mem_singleton.mpr he.symm
           · exact (hMate ⟨v,he⟩).elim
         have hCard:=card_le_card hSub
         rw [card_singleton] at hCard
         omega
   · have hEmpty: X=∅:= eq_empty_iff_forall_notMem.mpr (fun v hv=>hNonempty ⟨v,hv⟩)
     rw [hEmpty,card_empty]
     omega
 exact hGoal.trans (Nat.le_add_right A _)
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma M2.eH {S T: tI G M ell} {L A: ℕ}
   (hSize:∀r R,S.ND.state r=some R→ R.tree.vertices.card≤A)
   {es: List (Fin N ×Fin N)} (h: M2 true es (S.IX L) T)
   {x y: Fin N} (R: y7 T x y): R.state.tree.vertices.card≤A:= by
 obtain ⟨B,hB,hExt,hVertices,hHeld⟩:= h.CV R.root R.state R.present R.H9
 change (S.ND.state R.root).map (fun Q=>Q.IX L)=some B at hB
 obtain ⟨Q,hQ,hQB⟩:= Option.map_eq_some_iff.mp hB
 have hCard:=card_le_card hVertices
 rw [←hQB] at hCard
 exact hCard.trans (hSize R.root Q hQ)
lemma Ll.EJ {x y: Fin N} {E E': Finset (Fin N ×Fin N)}
   {S T: tI G M ell} (h: Ll true x y E S T E') (A L: ℕ)
   (hEndpoints: S.C4 E) (hRegional: Fm (S.ND.J9 E) E A L)
   (hReceivers:∀R: y7 S x y,R.state.tree.vertices.card≤A∧ R.state.tree.vertices.card≤L):
   Fm (T.ND.J9 E') E' A L:= by
 cases h with
 | augmentation R hFlag => exact hRegional.KF (S.bW R E)
 | extension hMode R hNo Q =>
   have hPlus:= g0 hRegional R.state.tree.vertices x y
     (fun u hu v hadj=>S.cK E hEndpoints R.state R.present R.H9 u v hu hadj)
     R.K5 (hReceivers R).1 (hReceivers R).2 (R.c9 E hEndpoints)
   exact hPlus.KF (Q.zU E)
 | skip hNo hNoExt => exact hRegional
lemma eU (base: tI G M ell) (L A: ℕ)
   (hSize:∀r R,base.ND.state r=some R→ R.tree.vertices.card≤A)
   (hHold: base.ND.Lm L)
   {S T: tI G M ell} {E F: Finset (Fin N ×Fin N)} {es: List (Fin N ×Fin N)}
   (h: Lk true es S E T F) (pre: List (Fin N ×Fin N))
   (hPre: M2 true pre (base.IX L) S)
   (hEndpoints: S.C4 E) (hRegional: Fm (S.ND.J9 E) E A L):
   Fm (T.ND.J9 F) F A L:= by
 induction h generalizing pre with
 | nil => exact hRegional
 | @cons x y es S U T E F H step rest ih =>
   have hLocal:= step.EJ A L hEndpoints hRegional (fun R=>
     ⟨hPre.eH hSize R,(hPre.lA hHold R).le⟩)
   exact ih (pre++[(x,y)]) (hPre.append (M2.cons step.Mi (M2.nil U)))
     (step.LD hEndpoints) hLocal
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma M2.p5 {S T: tI G M ell} {L A: ℕ}
   (hA: 2≤A) (hSize:∀r R,S.ND.state r=some R→ R.tree.vertices.card≤A)
   (hHold: S.ND.Lm L) {es: List (Fin N ×Fin N)}
   (h: M2 true es (S.IX L) T):
   ∀r R,T.ND.state r=some R→ R.tree.vertices.card≤A+L*ell:= by
 obtain ⟨F,hBirth⟩:= h.wZ ∅
 have hEmptyEnds:(S.IX L).C4 ∅:= by intro e he;simp at he
 have hEmptyActive:(S.IX L).ND.y4 ∅:= by intro e he;simp at he
 have hBeginSize:∀r R,(S.IX L).ND.state r=some R→ R.tree.vertices.card≤A:= by
   intro r R hR
   change (S.ND.state r).map (fun Q=>Q.IX L)=some R at hR
   obtain ⟨Q,hQ,hQR⟩:= Option.map_eq_some_iff.mp hR
   rw [←hQR]
   exact hSize r Q hQ
 have hInitialRegional:=(S.IX L).kP A L hA hBeginSize
 have hRegional:= eU S L A hSize hHold hBirth [] (M2.nil _) hEmptyEnds hInitialRegional
 have hCertificates:= hBirth.z1 hEmptyEnds hEmptyActive
 intro r R hR
 have hConn:= G8.jI T F R hR
 have hBound:= hRegional R.tree.vertices hConn
 have hCount:(F2 F R.tree.vertices).card≤ell:=
   T.ND.rK F hCertificates.2 ell T.labels T.labelled R hR
 exact hBound.trans (Nat.add_le_add_left (Nat.mul_le_mul_left L hCount) A)
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma tI.tO (S: tI G M ell) {a b: Fin N}
   (A: Lp G M a) (B: Lp G M b)
   (hA: S.ND.state a=some A) (hB: S.ND.state b=some B)
   (P: C3 G M) (hP: P.support⊆A.tree.vertices∪B.tree.vertices): P∉S.found:= by
 intro hFound
 have hMem:= P.mem_support 0 (by omega)
 have hRemoved:= S.Hu (mem_biUnion.mpr ⟨P,hFound,hMem⟩)
 have hCurrent:= hP hMem
 rcases mem_union.mp hCurrent with hCurrent|hCurrent
 · exact disjoint_left.mp (S.DO a A hA) hCurrent hRemoved
 · exact disjoint_left.mp (S.DO b B hB) hCurrent hRemoved
lemma tI.bU (S: tI G M ell) {x y: Fin N}
   (R: qF S x y):(S.sE R).found.card=S.found.card+1:= by
 change (insert _ S.found).card=S.found.card+1
 apply card_insert_of_notMem
 apply S.tO R.left R.right R.HJ R.GE
 exact R.left.tree.cR R.right.tree x y R.M1 R.head_mem R.path
lemma M3.EK {S T: tI G M ell} {mode: Bool} {x y: Fin N}
   (h: M3 mode x y S T) (size: ℕ)
   (hSize:∀r R,S.ND.state r=some R→ R.tree.vertices.card≤ size)
   (hBudget: S.Nm.card≤ 2*size*S.found.card): T.Nm.card≤ 2*size*T.found.card:= by
 cases h with
 | augmentation R hFlag =>
   have hL:=hSize R.ME R.left R.HJ
   have hR:=hSize R.L7 R.right R.GE
   have hCard:(S.sE R).Nm.card≤ S.Nm.card+R.left.tree.vertices.card+R.right.tree.vertices.card:= by
     change (S.Nm∪(R.left.tree.vertices∪R.right.tree.vertices)).card≤ _
     exact (card_union_le _ _).trans ((Nat.add_le_add_left (card_union_le _ _) _).trans_eq (by omega))
   rw [S.bU R]
   nlinarith
 | extension hMode R hNo A => cases A<;> exact hBudget
 | skip hNo hNoExt => exact hBudget
lemma M2.oP {S T: tI G M ell} {es: List (Fin N ×Fin N)}
   (h: M2 false es S T) (size: ℕ)
   (hSize:∀r R,S.ND.state r=some R→ R.tree.vertices.card≤ size)
   (hBudget: S.Nm.card≤ 2*size*S.found.card): T.Nm.card≤ 2*size*T.found.card:= by
 induction h with
 | nil => exact hBudget
 | cons step rest ih =>
   have hNewSize:= fun r R hR=>hSize r R (step.tS R hR)
   exact ih hNewSize (step.EK size hSize hBudget)
lemma b0 (base: tI G M ell) (L A: ℕ) (hA: 2≤ A)
   (hSize:∀r R,base.ND.state r=some R→ R.tree.vertices.card≤ A)
   (hHold: base.ND.Lm L)
   {S T: tI G M ell} {es: List (Fin N ×Fin N)} (h: M2 true es S T)
   (pre: List (Fin N ×Fin N)) (hPre: M2 true pre (base.IX L) S)
   (hBudget: S.Nm.card≤ 2*(A+L*ell)*S.found.card):
   T.Nm.card≤ 2*(A+L*ell)*T.found.card:= by
 induction h generalizing pre with
 | nil => exact hBudget
 | @cons x y es S U T step rest ih =>
   have hNowSize:=hPre.p5 hA hSize hHold
   have hNewBudget:=step.EK (A+L*ell) hNowSize hBudget
   exact ih (pre++[(x,y)]) (hPre.append (M2.cons step (M2.nil U))) hNewBudget
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
inductive Dd (mode: Bool) (x y: Fin N):
   tI G M ell→ tI G M ell→ Prop where
 | augmentation {S: tI G M ell} (R: qF S x y)
     (hflag: mode=true→ R.left.extended=false):
     Dd mode x y S (S.sE R)
 | extension {S: tI G M ell} (hmode: mode=true)
     (R: y7 S x y) (hNo:¬S.Bd x y true) (A: Bb R):
     Dd mode x y S A.Nj
lemma Dd.Mi {mode: Bool} {x y: Fin N} {S T: tI G M ell}
   (h: Dd mode x y S T): M3 mode x y S T:= by
 cases h with
 | augmentation R hflag => exact M3.augmentation R hflag
 | extension hmode R hNo A => exact M3.extension hmode R hNo A
lemma Dd.NB {mode: Bool} {x y: Fin N} {S T: tI G M ell}
   (h: Dd mode x y S T):
   T.LN+S.found.card+1≤ S.LN+T.found.card:= by
 cases h with
 | augmentation R hflag =>
   have hRank:(S.sE R).LN=S.LN:= rfl
   rw [hRank,S.bU R]
   omega
 | extension hmode R hNo A =>
   have hRank:=A.Ae
   have hFound: A.Nj.found=S.found:= by cases A<;> rfl
   rw [hFound]
   omega
inductive Dc (mode: Bool): List (Fin N ×Fin N)→
   tI G M ell→ tI G M ell→ Prop where
 | nil (S: tI G M ell): Dc mode [] S S
 | cons {x y: Fin N} {es: List (Fin N ×Fin N)} {S T U: tI G M ell}
     (step: Dd mode x y S T) (rest: Dc mode es T U):
     Dc mode ((x,y)::es) S U
lemma Dc.Mh {mode: Bool} {es: List (Fin N ×Fin N)}
   {S T: tI G M ell} (h: Dc mode es S T): M2 mode es S T:= by
 induction h with
 | nil S => exact M2.nil S
 | cons step rest ih => exact M2.cons step.Mi ih
lemma Dc.NB {mode: Bool} {es: List (Fin N ×Fin N)}
   {S T: tI G M ell} (h: Dc mode es S T):
   T.LN+S.found.card+es.length≤ S.LN+T.found.card:= by
 induction h with
 | nil S => simp
 | cons step rest ih =>
   have hh:=step.NB
   simp only [List.length_cons]
   omega
lemma dA (states: ℕ→ tI G M ell)
   (es: ℕ→ List (Fin N ×Fin N)) (mode: Bool)
   (hStep:∀t,Dc mode (es t) (states t) (states (t+1))) (T: ℕ):
   (∑t∈ range T,(es t).length)≤ 2*ell*matchingSize M+optimum G:= by
 have hTel:∀t,(states t).LN+(states 0).found.card+
     (∑i∈ range t,(es i).length)≤(states 0).LN+(states t).found.card:= by
   intro t
   induction t with
   | zero => simp
   | succ t ih =>
     have hCredit:=(hStep t).NB
     rw [sum_range_succ]
     omega
 have hRank:=(states 0).BU
 have hFound:=(states T).x3
 rw [(states T).Eu.2] at hFound
 have hh:=hTel T
 omega
lemma eK (states: ℕ→ tI G M ell)
   (es: ℕ→ List (Fin N ×Fin N)) (mode: Bool)
   (hStep:∀t,Dc mode (es t) (states t) (states (t+1)))
   (T: ℕ) (hT: 0<T):
   ∃t<T,T*(es t).length≤ 2*ell*matchingSize M+optimum G:= by
 by_contra hNone
 have hEvery:∀t∈range T,2*ell*matchingSize M+optimum G<T*(es t).length:= by
   intro t ht
   have ht':=mem_range.mp ht
   have hh:¬T*(es t).length≤ 2*ell*matchingSize M+optimum G:= fun h=>hNone ⟨t,ht',h⟩
   omega
 have hSum:=sum_lt_sum_of_nonempty (nonempty_range_iff.mpr (by omega: T≠0)) hEvery
 have hBudget:=dA states es mode hStep T
 simp only [sum_const,card_range,smul_eq_mul,←mul_sum] at hSum
 have hMult:=Nat.mul_le_mul_left T hBudget
 omega
end Be
end
noncomputable section
namespace Be.IO
inductive NR {D: IO} {ell: ℕ}
   (S: tI D.history.graph D.history.MG ell) (mode: Bool)
   (u v: Fin D.history.keys.card) where
 | augmentation (R: qF S u v) (flag: mode=true→ R.left.extended=false): NR S mode u v
 | extension (hmode: mode=true) (R: y7 S u v)
     (hNo:¬S.Bd u v true) (A: Bb R): NR S mode u v
namespace NR
variable {D: IO} {ell: ℕ} {S: tI D.history.graph D.history.MG ell}
   {mode: Bool} {u v: Fin D.history.keys.card}
def result (W: NR S mode u v): tI D.history.graph D.history.MG ell:=
 match W with
 | augmentation R _ => S.sE R
 | extension _ _ _ A => A.Nj
end NR
lemma JQ {D: IO} {ell: ℕ}
   (S: tI D.history.graph D.history.MG ell) (mode: Bool)
   (u v: Fin D.history.keys.card)
   (h: S.Bd u v mode∨(mode=true∧ Nonempty (y7 S u v))):
   Nonempty (NR S mode u v):= by
 by_cases hAug: S.Bd u v mode
 · obtain ⟨R,hFlag⟩:=hAug
   exact ⟨NR.augmentation R hFlag⟩
 · obtain ⟨hMode,⟨R⟩⟩:=h.resolve_left hAug
   have hNo:¬S.Bd u v true:=by simpa only [hMode] using hAug
   obtain ⟨A⟩:=Bb.FN R hNo
   exact ⟨NR.extension hMode R hNo A⟩
def Mx (D: IO) (ell: ℕ) (mode: Bool) (x y: ℕ): Prop:=
 ∃S,D.view ell=some S∧∃u v: Fin D.history.keys.card,
   D.history.identity u=x∧ D.history.identity v=y∧
   (D.node x).leader x≠(D.node y).leader y∧
   Nonempty (NR S mode u v)
def Fz (ell: ℕ) (mode: Bool): E9 Ln:=
 fun x y _ _ A B=>Mx (A∪B) ell mode x y
end Be.IO
end
noncomputable section
namespace Be.IO
variable (D: IO) (hConsistent: D.history.JS) (hClosed: D.history.JX) {ell: ℕ}
   (S: tI D.history.graph D.history.MG ell)
def It (r: Fin D.history.keys.card): Option tF:=
 if h:∃R,S.ND.state r=some R then
   some ⟨D.history,hConsistent,hClosed,r,h.choose,S.complete r h.choose h.choose_spec⟩ else none
def JD (u: Fin D.history.keys.card): Option tF:=
 (S.ND.owner u).bind (D.It hConsistent hClosed S)
def KM (u: Fin D.history.keys.card): Option ℕ:=
 (tB.NW D.history.identity D.history.identity_injective S.Et u).map D.history.identity
def JO (u: Fin D.history.keys.card) (old: Ln): Ln:=
 if old.Nm then old else
   { old with
     labels:=fun j=>if h:∃v,D.history.identity v=j then S.labels (u,h.choose) else old.labels j
     Nm:=decide (u∈S.Nm)
     Md:=D.KM S u
     L8:=D.JD hConsistent hClosed S u}
lemma yM (r: Fin D.history.keys.card) (R: Lp D.history.graph D.history.MG r)
   (hR: S.ND.state r=some R):
   D.It hConsistent hClosed S r=
     some ⟨D.history,hConsistent,hClosed,r,R,S.complete r R hR⟩:= by
 unfold It
 rw [dif_pos ⟨R,hR⟩]
 have hEq: Exists.choose (show ∃Q,S.ND.state r=some Q from ⟨R,hR⟩)=R:=
   Option.some.inj ((Exists.choose_spec (show ∃Q,S.ND.state r=some Q from ⟨R,hR⟩)).symm.trans hR)
 congr 2
lemma sS (r u: Fin D.history.keys.card) (R: Lp D.history.graph D.history.MG r)
   (hR: S.ND.state r=some R) (hU: u∈R.tree.vertices):
   D.JD hConsistent hClosed S u=
     some ⟨D.history,hConsistent,hClosed,r,R,S.complete r R hR⟩:= by
 unfold JD
 rw [(S.ND.KP r u).mpr ⟨R,hR,hU⟩,Option.bind_some]
 exact D.yM hConsistent hClosed S r R hR
end Be.IO
end
noncomputable section
namespace Ff
structure State (K I L R: Type) where
 parameters: K
 NN: ℕ
 original: I
 elapsed: ℕ
 left: L
 right: R
section Sequence
variable {K I O J P: Type}
   (A: Deterministic K I O) (B: Deterministic K J P)
   (prepare: K→ ℕ→ I→ O→ J)
def Ir (k: K) (id: ℕ) (inp: I): B.program.State:=
 B.program.init k id (prepare k id inp (A.program.out (A.program.init k id inp (fun _=> false)))) (fun _=> false)
def sequence: Deterministic K I P where
 program:={
   State:= State K I A.program.State B.program.State
   Msg:= A.program.Msg ×B.program.Msg
   rounds:= fun k=> A.program.rounds k+1+B.program.rounds k
   init:= fun k id inp _=>⟨k,id,inp,0,A.program.init k id inp (fun _=> false),Ir A B prepare k id inp⟩
   send:= fun st=>(A.program.send st.left,B.program.send st.right)
   step:= fun st msgs=>
     if st.elapsed< A.program.rounds st.parameters then
       {st with elapsed:= st.elapsed+1,left:= A.program.step st.left (msgs.map Prod.fst)}
     else if st.elapsed= A.program.rounds st.parameters then
       {st with elapsed:= st.elapsed+1,right:= B.program.init st.parameters st.NN (prepare st.parameters st.NN st.original (A.program.out st.left)) (fun _=> false)}
     else {st with elapsed:= st.elapsed+1,right:= B.program.step st.right (msgs.map Prod.snd)}
   out:= fun st=> B.program.out st.right}
 tape_independent:= by intros; rfl
variable {V: Type} [Fintype V] (H: SimpleGraph V) (k: K) (ids: V→ ℕ) (inp: V→ I)
lemma MV (t: ℕ) (ht: t≤ A.program.rounds k):∀v,
   (sequence A B prepare).program.run H k ids inp (fun _ _=> false) t v=
     ⟨k,ids v,inp v,t,A.program.run H k ids inp (fun _ _=> false) t v,Ir A B prepare k (ids v) (inp v)⟩:= by
 induction t with
 | zero => intro v; rfl
 | succ t ih =>
   intro v
   have htt: t< A.program.rounds k:= by omega
   have hi:= ih (by omega)
   conv_lhs=> rw [SmoothedMIS.LocalAlg.run]
   simp only [hi]
   dsimp only [sequence]
   rw [if_pos htt]
   simp only [SmoothedMIS.LocalAlg.run,Multiset.map_map,Function.comp_def]
abbrev L0: V→ J:= fun v=> prepare k (ids v) (inp v)
 (A.program.output H k ids inp (fun _ _=> false) v)
lemma Mb (t: ℕ):∀v,
   (sequence A B prepare).program.run H k ids inp (fun _ _=> false) (A.program.rounds k+1+t) v=
     ⟨k,ids v,inp v,A.program.rounds k+1+t,
       A.program.run H k ids inp (fun _ _=> false) (A.program.rounds k) v,
       B.program.run H k ids (L0 A prepare H k ids inp) (fun _ _=> false) t v⟩:= by
 induction t with
 | zero =>
   intro v
   simp only [Nat.add_zero]
   conv_lhs=> rw [SmoothedMIS.LocalAlg.run]
   simp only [MV A B prepare H k ids inp _ le_rfl]
   dsimp only [sequence]
   simp only [lt_self_iff_false,ite_false,ite_true]
   rfl
 | succ t ih =>
   intro v
   rw [show A.program.rounds k+1+(t+1)=(A.program.rounds k+1+t)+1 by omega,SmoothedMIS.LocalAlg.run]
   simp only [ih]
   dsimp only [sequence]
   have hlt:¬(A.program.rounds k+1+t< A.program.rounds k):= by omega
   have heq:¬(A.program.rounds k+1+t= A.program.rounds k):= by omega
   simp only [if_neg hlt,if_neg heq]
   simp only [SmoothedMIS.LocalAlg.run,Multiset.map_map,Function.comp_def]
lemma CM (v: V):
   (sequence A B prepare).program.output H k ids inp (fun _ _=> false) v=
     B.program.output H k ids (L0 A prepare H k ids inp) (fun _ _=> false) v:= by
 unfold SmoothedMIS.LocalAlg.output
 change B.program.out ((sequence A B prepare).program.run H k ids inp (fun _ _=> false)
   (A.program.rounds k+1+B.program.rounds k) v).right= _
 rw [Mb]
end Sequence
end Ff
end
noncomputable section
namespace C7
variable {K I O J P: Type}
def NE (A: Deterministic K I O) (k: K): Deterministic Unit I O where
 program:={
   State:= A.program.State
   Msg:= A.program.Msg
   rounds:= fun _=> A.program.rounds k
   init:= fun _ id inp _=> A.program.init k id inp (fun _=> false)
   send:= A.program.send
   step:= A.program.step
   out:= A.program.out}
 tape_independent:= by intros; rfl
lemma Ko (A: Deterministic K I O) (k: K) {V: Type} [Fintype V] (H: SimpleGraph V)
   (ids: V→ ℕ) (inp: V→ I) (t: ℕ):∀v,
   (NE A k).program.run H () ids inp (fun _ _=> false) t v=
     A.program.run H k ids inp (fun _ _=> false) t v:= by
 induction t with
 | zero => intro v; rfl
 | succ t ih =>
   intro v
   rw [SmoothedMIS.LocalAlg.run,SmoothedMIS.LocalAlg.run]
   simp only [ih]
   rfl
lemma FS (A: Deterministic K I O) (k: K) {V: Type} [Fintype V] (H: SimpleGraph V)
   (ids: V→ ℕ) (inp: V→ I) (v: V):
   (NE A k).program.output H () ids inp (fun _ _=> false) v=
     A.program.output H k ids inp (fun _ _=> false) v:= by
 unfold SmoothedMIS.LocalAlg.output
 rw [Ko]
 rfl
def transform (A: Deterministic Unit J O) (pre: ℕ→ I→ J) (post: ℕ→ I→ O→ P): Deterministic Unit I P where
 program:={
   State:= ℕ ×I ×A.program.State
   Msg:= A.program.Msg
   rounds:= A.program.rounds
   init:= fun _ id inp _=>(id,inp,A.program.init () id (pre id inp) (fun _=> false))
   send:= fun st=> A.program.send st.2.2
   step:= fun st msgs=>(st.1,st.2.1,A.program.step st.2.2 msgs)
   out:= fun st=> post st.1 st.2.1 (A.program.out st.2.2)}
 tape_independent:= by intros; rfl
lemma GU (A: Deterministic Unit J O) (pre: ℕ→ I→ J) (post: ℕ→ I→ O→ P)
   {V: Type} [Fintype V] (H: SimpleGraph V) (ids: V→ ℕ) (inp: V→ I) (t: ℕ):∀v,
   (transform A pre post).program.run H () ids inp (fun _ _=> false) t v=
     (ids v,inp v,A.program.run H () ids (fun v=> pre (ids v) (inp v)) (fun _ _=> false) t v):= by
 induction t with
 | zero => intro v; rfl
 | succ t ih =>
   intro v
   rw [SmoothedMIS.LocalAlg.run,SmoothedMIS.LocalAlg.run]
   simp only [ih]
   rfl
lemma A4 (A: Deterministic Unit J O) (pre: ℕ→ I→ J) (post: ℕ→ I→ O→ P)
   {V: Type} [Fintype V] (H: SimpleGraph V) (ids: V→ ℕ) (inp: V→ I) (v: V):
   (transform A pre post).program.output H () ids inp (fun _ _=> false) v=
     post (ids v) (inp v) (A.program.output H () ids (fun v=> pre (ids v) (inp v)) (fun _ _=> false) v):= by
 unfold SmoothedMIS.LocalAlg.output
 rw [GU]
 rfl
def pointwise (f: ℕ→ I→ O): Deterministic Unit I O where
 program:={
   State:= O
   Msg:= Unit
   rounds:= fun _=> 0
   init:= fun _ id inp _=> f id inp
   send:= fun _=>()
   step:= fun st _=> st
   out:= id}
 tape_independent:= by intros; rfl
end C7
end
noncomputable section
namespace Be
variable {I: Type}
def Gq (s: ℕ): Deterministic Unit (ℕ ×I) (ℕ ×Nw I):=
 C7.transform (C7.NE (collect I) s) (fun _ inp=> inp) (fun _ inp R=>(inp.1,R))
def Br (rule: E9 I): Deterministic Unit (ℕ ×Nw I) (ℕ ×Finset ℕ):=
 Fd.MN (fun id inp msgs=>(inp.1,Dn rule id inp msgs))
def JE (s: ℕ): Deterministic Unit (ℕ ×Finset ℕ) (Finset ℕ):=
 C7.transform (C7.NE (collect (Finset ℕ)) s) (fun _ inp=> inp)
   (fun id inp R=> if id= inp.1 then (R.biUnion Prod.snd).filter (fun j=> j≠ id) else ∅)
def mA (s: ℕ) (rule: E9 I): Deterministic Unit (ℕ ×I) (Finset ℕ):=
 Ff.sequence (Gq s)
   (Ff.sequence (Br rule) (JE s) (fun _ _ _ out=> out)) (fun _ _ _ out=> out)
lemma b7 (s: ℕ) (rule: E9 I):
   (mA s rule).program.rounds ()= 2*s+3:= by
 change s+1+(1+1+s)= 2*s+3
 omega
namespace tE
variable {N: ℕ} {G: SimpleGraph (Fin N)} {s: ℕ} (P: tE G s)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (inp: Fin N→ I)
include hi in
lemma nH (v: Fin N):
   execute (Gq s) G () ids (fun v=>(ids (P.leader v),inp v)) v=(ids (P.leader v),P.NI ids inp v):= by
 unfold execute Gq
 rw [C7.A4,C7.FS,P.I0 ids hi inp]
 rfl
lemma iJ (rule: E9 I) (v: Fin N):
   execute (Br rule) G () ids (fun v=>(ids (P.leader v),P.NI ids inp v)) v=
     (ids (P.leader v),P.BZ ids inp rule v):= by
 unfold execute Br
 rw [Fd.Cn]
 rw [P.j5 ids inp rule v]
include hi in
lemma sT (rule: E9 I) (v: Fin N):
   execute (JE s) G () ids (fun v=>(ids (P.leader v),P.BZ ids inp rule v)) v=
     P.EQ ids inp rule v:= by
 letI: DecidableEq (Finset ℕ):= Classical.decEq _
 unfold execute JE
 rw [C7.A4,C7.FS,P.I0 ids hi (P.BZ ids inp rule)]
 simp only [image_biUnion,Function.comp_def]
 rfl
include hi in
lemma bX (rule: E9 I):
   execute (mA s rule) G () ids (fun v=>(ids (P.leader v),inp v))=
     neighborIDs (P.Lv (P.Lx ids inp rule) (P.Dr ids inp rule)) ids:= by
 have hp: execute (Gq s) G () ids (fun v=>(ids (P.leader v),inp v))=
     fun v=>(ids (P.leader v),P.NI ids inp v):= funext (P.nH ids hi inp)
 have hb: execute (Br rule) G () ids (fun v=>(ids (P.leader v),P.NI ids inp v))=
     fun v=>(ids (P.leader v),P.BZ ids inp rule v):= funext (P.iJ ids inp rule)
 funext v
 unfold execute mA
 rw [Ff.CM]
 change (Ff.sequence (Br rule) (JE s) (fun _ _ _ out=> out)).program.output G () ids
   (execute (Gq s) G () ids (fun v=>(ids (P.leader v),inp v))) (fun _ _=> false) v= _
 rw [hp,Ff.CM]
 change execute (JE s) G () ids
   (execute (Br rule) G () ids (fun v=>(ids (P.leader v),P.NI ids inp v))) v= _
 rw [hb,P.sT ids hi inp rule v,P.lH ids inp hi rule v]
end tE
end Be
end
noncomputable section
namespace Fb
abbrev Nx (I: Type):= ℕ ×I ×Finset ℕ
def Kh {I: Type} (R: Finset (Nx I)) (j: ℕ): Option (Nx I):=
 if h:∃z∈ R,z.1= j then some h.choose else none
def H6 {I: Type} (z: Nx I): Finset ℕ:= z.2.2
def MW {K I O: Type} (A: Deterministic K I O) (k: K)
   (R: Finset (Nx I)): ℕ→ ℕ→ Option A.program.State
 | 0,j => (Kh R j).map fun z=> A.program.init k j z.2.1 (fun _=> false)
 | t+1,j => (Kh R j).bind fun z=>
     (MW A k R t j).map fun s=> A.program.step s
       ((H6 z).val.filterMap fun b=>(MW A k R t b).map A.program.send)
structure JU (K I: Type) where
 LM: K
 Ku: ℕ
 Nk: Finset (Nx I)
def merge {I: Type} (R: Finset (Nx I)) (msgs: Multiset (Finset (Nx I))): Finset (Nx I):=
 R ∪msgs.toFinset.biUnion id
def Me {K I O: Type} (A: Deterministic K I O):
   Deterministic (K ×ℕ) (Finset (Nx I)) (ℕ→ Option O) where
 program:={
   State:= JU K I
   Msg:= Finset (Nx I)
   rounds:= fun k=>(k.2+1)* A.program.rounds k.1
   init:= fun k _ inp _=>⟨k.1,A.program.rounds k.1,inp⟩
   send:= JU.Nk
   step:= fun s msgs=>{s with Nk:= merge s.Nk msgs}
   out:= fun s j=>(MW A s.LM s.Nk s.Ku j).map A.program.out}
 tape_independent:= by intros; rfl
variable {N: ℕ} {G: SimpleGraph (Fin N)} {V I: Type} [Fintype V]
   (D: Routed G V) (ids: Fin N→ ℕ) (inp: V→ I)
def NJ (a: V): Nx I:=
 (D.identity a,inp a,(univ.filter (D.graph.Adj a)).image D.identity)
def HL (v: Fin N): Finset (Nx I):=
 (univ.filter (fun a=> D.owner a= v)).image (NJ D inp)
lemma Jx (a: V):
   H6 (NJ D inp a)=(univ.filter (D.graph.Adj a)).image D.identity:= rfl
lemma I5 {R: Finset (Nx I)} (hauth:∀z∈ R,∃a,NJ D inp a= z)
   (a: V) (ha: NJ D inp a∈ R):
   Kh R (D.identity a)= some (NJ D inp a):= by
 unfold Kh
 have hex:∃z∈ R,z.1= D.identity a:=⟨NJ D inp a,ha,rfl⟩
 rw [dif_pos hex]
 congr 1
 have hmem:= hex.choose_spec.1
 obtain ⟨b,hb⟩:= hauth _ hmem
 have heq: D.identity b= D.identity a:= by
   change (NJ D inp b).1= _
   rw [hb]
   exact hex.choose_spec.2
 rw [←hb,D.identity_injective heq]
def NK: ℕ→ Fin N→ Finset (Nx I)
 | 0,v => HL D inp v
 | t+1,v => merge (NK t v)
     ((univ.filter (G.Adj v)).val.map fun w=> NK t w)
lemma DN (t: ℕ) (v: Fin N) (z: Nx I):
   z∈ NK D inp (t+1) v↔ z∈ NK D inp t v∨
     ∃w,G.Adj v w∧ z∈ NK D inp t w:= by
 simp only [NK,merge,mem_union,mem_biUnion,Multiset.mem_toFinset,Multiset.mem_map,
   mem_val,mem_filter,mem_univ,true_and,id_eq]
 aesop
lemma Kk (v: Fin N): Monotone (fun t=> NK D inp t v):= by
 apply monotone_nat_of_le_succ
 intro t z hz
 exact (DN D inp t v z).mpr (Or.inl hz)
lemma BL (t: ℕ):
   ∀v z,z∈ NK D inp t v→∃a,NJ D inp a= z:= by
 induction t with
 | zero =>
   intro v z hz
   obtain ⟨a,ha,rfl⟩:= mem_image.mp hz
   exact ⟨a,rfl⟩
 | succ t ih =>
   intro v z hz
   rcases (DN D inp t v z).mp hz with h| ⟨w,hw,hz⟩
   · exact ih v z h
   · exact ih w z hz
lemma Cw (a: V) {v u: Fin N} (w: G.Walk v u) (hu: u= D.owner a):
   NJ D inp a∈ NK D inp w.length v:= by
 induction w with
 | nil =>
   apply mem_image.mpr
   exact ⟨a,mem_filter.mpr ⟨mem_univ a,hu.symm⟩,rfl⟩
 | cons h w ih =>
   apply (DN D inp w.length _ _).mpr
   exact Or.inr ⟨_,h,ih hu⟩
lemma gZ (t: ℕ) (a: V) (v: Fin N) (h: Close G t v (D.owner a)):
   NJ D inp a∈ NK D inp t v:= by
 obtain ⟨w,hw⟩:= h
 exact Kk D inp v hw (Cw D inp a w rfl)
lemma Gu (r: ℕ) (hr: RouteLength D r) {a b: V} (w: D.graph.Walk a b):
   ∃path: G.Walk (D.owner a) (D.owner b),path.length≤ r* w.length:= by
 induction w with
 | nil => exact ⟨.nil,by simp⟩
 | @cons a b c h w ih =>
   obtain ⟨path,hpath⟩:= ih
   refine ⟨(D.route a b h).append path,?_⟩
   rw [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_cons]
   have hh:= hr a b h
   nlinarith
lemma Ez (r: ℕ) (hr: RouteLength D r) (t: ℕ) (a b: V)
   (h: Close D.graph t a b): Close G (r*t) (D.owner a) (D.owner b):= by
 obtain ⟨w,hw⟩:= h
 obtain ⟨path,hpath⟩:= Gu D r hr w
 exact ⟨path,hpath.trans (Nat.mul_le_mul_left r hw)⟩
lemma filterMap_congr {α β: Type*} {s: Multiset α} {f g: α→ Option β}
   (h:∀a∈ s,f a= g a): s.filterMap f= s.filterMap g:= by
 induction s using Multiset.induction_on with
 | empty => rfl
 | @cons a s ih =>
   rw [Multiset.filterMap_cons,Multiset.filterMap_cons,h a (by simp)]
   rw [ih (fun b hb=> h b (by simp [hb]))]
lemma AU {K O: Type} (A: Deterministic K I O) (k: K)
   (R: Finset (Nx I)) (hauth:∀z∈ R,∃b,NJ D inp b= z)
   (t: ℕ) (a: V)
   (hall:∀b,Close D.graph t a b→ NJ D inp b∈ R):
   MW A k R t (D.identity a)=
     some (A.program.run D.graph k D.identity inp (fun _ _=> false) t a):= by
 induction t generalizing a with
 | zero =>
   have hself: NJ D inp a∈ R:= hall a ⟨.nil,by simp⟩
   rw [MW,I5 D inp hauth a hself]
   rfl
 | succ t ih =>
   have hself: NJ D inp a∈ R:= hall a ⟨.nil,by simp⟩
   have hprev:∀b,Close D.graph t a b→ NJ D inp b∈ R:= by
     intro b hb
     obtain ⟨w,hw⟩:= hb
     exact hall b ⟨w,by omega⟩
   have hneighbor (b: V) (hb: D.graph.Adj a b):
       MW A k R t (D.identity b)=
         some (A.program.run D.graph k D.identity inp (fun _ _=> false) t b):= by
     apply ih
     intro c hc
     obtain ⟨w,hw⟩:= hc
     exact hall c ⟨.cons hb w,by simpa using Nat.succ_le_succ hw⟩
   rw [MW,I5 D inp hauth a hself,Option.bind_some,
     ih a hprev,Option.map_some]
   congr 1
   rw [Jx]
   rw [image_val_of_injOn (fun b _ c _ h=> D.identity_injective h),Multiset.filterMap_map]
   have heq:∀b∈(univ.filter (D.graph.Adj a)).val,
       (MW A k R t (D.identity b)).map A.program.send=
         some (A.program.send (A.program.run D.graph k D.identity inp (fun _ _=> false) t b)):= by
     intro b hb
     have hadj:=(mem_filter.mp hb).2
     rw [hneighbor b hadj]
     rfl
   simp only [Function.comp_def]
   rw [filterMap_congr heq]
   change A.program.step _ (Multiset.filterMap (some ∘
     (fun b=> A.program.send (A.program.run D.graph k D.identity inp (fun _ _=> false) t b))) _)= _
   rw [Multiset.filterMap_eq_map]
   rfl
lemma GJ {K O: Type} (A: Deterministic K I O) (k: K) (r t: ℕ) (v: Fin N):
   (Me A).program.run G (k,r) ids (HL D inp) (fun _ _=> false) t v=
     ⟨k,A.program.rounds k,NK D inp t v⟩:= by
 induction t generalizing v with
 | zero => rfl
 | succ t ih =>
   rw [SmoothedMIS.LocalAlg.run]
   simp only [ih]
   rfl
lemma yQ {K O: Type} (A: Deterministic K I O) (k: K) (r: ℕ) (hr: RouteLength D r) (a: V):
   execute (Me A) G (k,r) ids (HL D inp) (D.owner a) (D.identity a)=
     some (A.program.output D.graph k D.identity inp (fun _ _=> false) a):= by
 unfold execute SmoothedMIS.LocalAlg.output
 rw [GJ]
 change (MW A k (NK D inp ((r+1)*A.program.rounds k) (D.owner a))
   (A.program.rounds k) (D.identity a)).map A.program.out= _
 rw [AU D inp A k _ (BL D inp _ (D.owner a)) (A.program.rounds k) a ?_]
 · rfl
 · intro b hb
   apply gZ
   obtain ⟨path,hpath⟩:= Ez D r hr (A.program.rounds k) a b hb
   exact ⟨path,hpath.trans (Nat.mul_le_mul_right _ (Nat.le_succ r))⟩
end Fb
end
noncomputable section
namespace Be
variable {K: Type}
def Ge (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K) (r: ℕ):
   Deterministic Unit (Finset ℕ) (Option ℕ):=
 C7.transform (C7.NE (Fb.Me A) (k,r))
   (fun id neighbors=>{(id,neighbors,neighbors)})
   (fun id _ out=>(out id).join)
lemma pH (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K) (r: ℕ):
   (Ge A k r).program.rounds ()=(r+1)*A.program.rounds k:= rfl
lemma nE (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K) (r: ℕ)
   {N: ℕ} (G H: SimpleGraph (Fin N)) (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (hr:∀u v,H.Adj u v→ Close G r u v):
   execute (Ge A k r) G () ids (neighborIDs H ids)= execute A H k ids (neighborIDs H ids):= by
 let D: Routed G (Fin N):={
   graph:= H
   owner:= id
   identity:= ids
   identity_injective:= hi
   route:= fun u v h=>(hr u v h).choose}
 have hD: RouteLength D r:= fun u v h=>(hr u v h).choose_spec
 have hinp:(fun v=>({(ids v,neighborIDs H ids v,neighborIDs H ids v)}: Finset (Fb.Nx (Finset ℕ))))=
     Fb.HL D (neighborIDs H ids):= by
   funext v
   simp only [Fb.HL,D,id_eq,filter_eq',mem_univ,if_true,image_singleton,Fb.NJ]
   have hn: H.neighborFinset v= univ.filter (H.Adj v):= by ext w;simp
   simp only [neighborIDs,hn]
 funext v
 unfold execute Ge
 rw [C7.A4,C7.FS,hinp]
 have hout:= Fb.yQ D ids (neighborIDs H ids) A k r hD v
 exact (congrArg Option.join hout).trans rfl
end Be
end
noncomputable section
namespace Be
variable {I: Type}
def KR (s: ℕ): Deterministic Unit (ℕ ×I ×Option ℕ) (ℕ ×I):=
 C7.transform (C7.NE (collect (I ×Option ℕ)) s)
   (fun _ inp=>(inp.1,inp.2))
   (fun _ inp R=>(IH inp.1 ((lookup R inp.1).bind Prod.snd),inp.2.1))
def Hl (s: ℕ): Deterministic Unit (ℕ ×I ×Option ℕ) (Finset (ℕ ×I)):=
 Ff.sequence (KR s) (C7.NE (collect I) (2*s)) (fun _ _ _ out=> out)
lemma qX (s: ℕ):(Hl (I:=I) s).program.rounds ()= 3*s+1:= by
 change s+1+2*s= 3*s+1
 omega
namespace tE
variable {N: ℕ} {G: SimpleGraph (Fin N)} {s: ℕ} (P: tE G s)
   (Lx: Fin N→ Fin N→ Prop) (hC: Symmetric Lx)
   (R: SimpleGraph (Fin N)) (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (out: Fin N→ Option ℕ) (hout: ReportsMatching (P.Lv Lx hC) ids out R) (inp: Fin N→ I)
include hout in
lemma u8 (v: Fin N):
   execute (KR s) G () ids (fun v=>(ids (P.leader v),inp v,out v)) v=
     (ids (P.HY R ids hi v),inp v):= by
 letI: DecidableEq (I ×Option ℕ):= Classical.decEq _
 unfold execute KR
 rw [C7.A4,C7.FS]
 change (IH (ids (P.leader v)) ((lookup
   ((collect (I ×Option ℕ)).program.output G s ids (fun w=>(ids (P.leader w),inp w,out w)) (fun _ _=> false) v)
   (ids (P.leader v))).bind Prod.snd),inp v)= _
 rw [P.I0 ids hi (fun w=>(inp w,out w)) v]
 let T:=(univ.filter (fun w=> P.leader w= P.leader v)).image (fun w=>(ids w,(inp w,out w)))
 have hauth:∀r∈ T,∃w,r=(ids w,(inp w,out w)):= by
   intro r hr
   obtain ⟨w,hw,heq⟩:= mem_image.mp hr
   exact ⟨w,heq.symm⟩
 have hmem:(ids (P.leader v),(inp (P.leader v),out (P.leader v)))∈ T:=
   mem_image.mpr ⟨P.leader v,mem_filter.mpr ⟨mem_univ _,P.fixed v⟩,rfl⟩
 have hlook:= Ea T ids (fun w=>(inp w,out w)) hi hauth (P.leader v) hmem
 rw [hlook]
 simp only [Option.bind_some]
 rw [qE (P.Lv Lx hC) R ids hi out hout (P.leader v)]
 rfl
include hout in
lemma oR (v: Fin N):
   execute (Hl s) G () ids (fun v=>(ids (P.leader v),inp v,out v)) v=
     (univ.filter (fun w=> P.HY R ids hi w= P.HY R ids hi v)).image (fun w=>(ids w,inp w)):= by
 have hinp: execute (KR s) G () ids (fun v=>(ids (P.leader v),inp v,out v))=
     fun v=>(ids (P.HY R ids hi v),inp v):= funext (P.u8 Lx hC R ids hi out hout inp)
 unfold execute Hl
 rw [Ff.CM,C7.FS]
 change (collect I).program.output G (2*s) ids
   (execute (KR s) G () ids (fun v=>(ids (P.leader v),inp v,out v))) (fun _ _=> false) v= _
 rw [hinp]
 exact (P.merge Lx hC R hout.1 ids hi).I0 ids hi inp v
end tE
end Be
end
noncomputable section
namespace Be
variable {K I: Type}
def BC (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K) (s: ℕ) (rule: E9 I):
   Deterministic Unit (ℕ ×I) (Option ℕ):=
 Ff.sequence (mA s rule) (Ge A k (2*s+1)) (fun _ _ _ out=> out)
lemma kA (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K) (s: ℕ) (rule: E9 I):
   (BC A k s rule).program.rounds ()= 2*s+4+(2*s+2)*A.program.rounds k:= by
 change (mA s rule).program.rounds ()+1+(Ge A k (2*s+1)).program.rounds ()= _
 rw [b7,pH]
def KS (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K) (s: ℕ) (rule: E9 I):
   Deterministic Unit (ℕ ×I) (Nw I):=
 Ff.sequence (BC A k s rule) (Hl s) (fun _ _ inp out=>(inp.1,inp.2,out))
lemma x5 (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K) (s: ℕ) (rule: E9 I):
   (KS A k s rule).program.rounds ()= 5*s+6+(2*s+2)*A.program.rounds k:= by
 change (BC A k s rule).program.rounds ()+1+(Hl (I:=I) s).program.rounds ()= _
 rw [kA,qX]
 omega
namespace tE
variable {N: ℕ} {G: SimpleGraph (Fin N)} {s: ℕ} (P: tE G s)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (inp: Fin N→ I)
include hi in
lemma iQ (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K) (rule: E9 I):
   execute (BC A k s rule) G () ids (fun v=>(ids (P.leader v),inp v))=
     execute A (P.Lv (P.Lx ids inp rule) (P.Dr ids inp rule)) k ids
       (neighborIDs (P.Lv (P.Lx ids inp rule) (P.Dr ids inp rule)) ids):= by
 funext v
 unfold execute BC
 rw [Ff.CM]
 change execute (Ge A k (2*s+1)) G () ids
   (execute (mA s rule) G () ids (fun v=>(ids (P.leader v),inp v))) v= _
 rw [P.bX ids hi inp rule]
 rw [nE A k (2*s+1) G _ ids hi (P.Bp _ _)]
 rfl
include hi in
lemma u9 (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K) (rule: E9 I)
   (R: SimpleGraph (Fin N))
   (hR: ReportsMatching (P.Lv (P.Lx ids inp rule) (P.Dr ids inp rule)) ids
     (execute A (P.Lv (P.Lx ids inp rule) (P.Dr ids inp rule)) k ids
       (neighborIDs (P.Lv (P.Lx ids inp rule) (P.Dr ids inp rule)) ids)) R) (v: Fin N):
   execute (KS A k s rule) G () ids (fun v=>(ids (P.leader v),inp v)) v=
     (univ.filter (fun w=> P.HY R ids hi w= P.HY R ids hi v)).image (fun w=>(ids w,inp w)):= by
 unfold execute KS
 rw [Ff.CM]
 change execute (Hl s) G () ids (fun v=>(ids (P.leader v),inp v,
   execute (BC A k s rule) G () ids (fun v=>(ids (P.leader v),inp v)) v)) v= _
 rw [P.iQ ids hi inp A k rule]
 exact P.oR _ _ R ids hi _ hR inp v
end tE
end Be
end
noncomputable section
namespace Be.IO
structure JR (D: IO) (ell: ℕ) (mode external: Bool) where
 state: tI D.history.graph D.history.MG ell
 valid: D.view ell=some state
 tail: Fin D.history.keys.card
 head: Fin D.history.keys.card
 cross: external=true→
   (D.node (D.history.identity tail)).leader (D.history.identity tail)≠
     (D.node (D.history.identity head)).leader (D.history.identity head)
 NY: NR state mode tail head
def Kc (D: IO) (ell: ℕ) (mode external: Bool): Option (JR D ell mode external):=
 if h: Nonempty (JR D ell mode external) then some h.some else none
def Lt (D: IO) (ell: ℕ) (mode external: Bool) (j: ℕ) (old: Ln): Ln:=
 if hConsistent: D.history.JS then
   if hClosed: D.history.JX then
     match D.Kc ell mode external with
     | none=>old
     | some W=>if h:∃u,D.history.identity u=j then
         D.JO hConsistent hClosed W.NY.result h.choose old else old
   else old
 else old
lemma wO (D: IO) (ell: ℕ) (mode external: Bool)
   (h: Nonempty (JR D ell mode external)):∃W,D.Kc ell mode external=some W:= by
 unfold Kc
 rw [dif_pos h]
 exact ⟨h.some,rfl⟩
lemma BG (D: IO) (ell: ℕ) (mode: Bool) (x y: ℕ)
   (hEdge: D.Mx ell mode x y): Nonempty (JR D ell mode true):= by
 obtain ⟨S,hS,u,v,hU,hV,hCross,⟨W⟩⟩:=hEdge
 refine ⟨⟨S,hS,u,v,?_,W⟩⟩
 intro h
 simpa only [hU,hV] using hCross
end IO
variable {K: Type}
def x6 (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   (size ell: ℕ) (mode: Bool): Deterministic Unit Ln Ln:=
 C7.transform (KS A k size (IO.Fz ell mode))
   (fun j z=>(z.leader j,z))
   (fun j old NI=>IO.Lt NI ell mode true j old)
lemma gT (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   (size ell: ℕ) (mode: Bool):
   (x6 A k size ell mode).program.rounds ()=5*size+6+(2*size+2)*A.program.rounds k:=
 x5 A k size (IO.Fz ell mode)
def rM (size ell: ℕ): Deterministic Unit Ln Ln:=
 C7.transform (C7.NE (collect Ln) size)
   (fun j z=>(z.leader j,z))
   (fun j old NI=>IO.Lt NI ell true false j old)
lemma d6 (size ell: ℕ):
   (rM size ell).program.rounds ()=size:=rfl
end Be
noncomputable section
namespace Be.IO
def omission (D: IO) (ell: ℕ) (extension: Bool) (x y: ℕ): Prop:=
 ∃S,D.view ell=some S∧∃u v: Fin D.history.keys.card,
   D.history.identity u=x∧ D.history.identity v=y∧
   (D.node x).leader x≠(D.node y).leader y∧
   (if extension then Nonempty (y7 S u v)∨ Nonempty (y7 S v u)
     else S.Bd u v false∨ S.Bd v u false)
end IO
def AC (ell: ℕ) (extension: Bool) (j: ℕ) (own: ℕ ×Nw Ln)
   (messages: Multiset (ℕ ×ℕ ×Nw Ln)): Finset ℕ:=
 (messages.toFinset.filter (fun m=>IO.omission (own.2∪m.2.2) ell extension j m.1)).image Prod.fst
def yE (size ell: ℕ) (extension: Bool): Deterministic Unit Ln Ln:=
 C7.transform
   (Ff.sequence (Gq size)
     (Fd.MN (AC ell extension)) (fun _ _ _ z=>z))
   (fun j z=>(z.leader j,z))
   (fun _ old omitted=>{old with ignored:=old.ignored∪omitted})
lemma gY (size ell: ℕ) (extension: Bool):
   (yE size ell extension).program.rounds ()=size+2:=rfl
end Be
noncomputable section
namespace Be.Bi
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)}
   (E: wF G M H K) {r: Fin N} (S: Bi G M r)
lemma bT (C: Finset (Fin N ×Fin N)) (D: Finset (Fin P ×Fin P))
   (hC:∀u v,(u,v)∈C→ G.Adj u v) (hD:∀u v,(u,v)∈D→ H.Adj u v)
   (hEdges:∀u∈S.vertices,∀v∈S.vertices,(E.toFun u,E.toFun v)∈D↔(u,v)∈C):
   (S.FX C hC).Nd E=(S.Nd E).FX D hD:= by
 apply Bi.FJ
 apply Subset.antisymm
 · intro a ha
   change a∈(S.NS∪S.Dq C).image E.pairMap at ha
   obtain ⟨⟨u,v⟩,hLocal,hEq⟩:=mem_image.mp ha
   subst a
   rcases mem_union.mp hLocal with hOld|hNew
   · exact mem_union_left _ ((E.Jn S.NS u v).mpr hOld)
   · obtain ⟨hC',hM,hu,hv⟩:=mem_filter.mp hNew
     exact mem_union_right _ (mem_filter.mpr ⟨(hEdges u hu v hv).mpr hC',
       fun hm=>hM ((E.HS u v).mp hm),
       (S.Aj E).symm ▸mem_image.mpr ⟨u,hu,rfl⟩,
       (S.Aj E).symm ▸mem_image.mpr ⟨v,hv,rfl⟩⟩)
 · rintro ⟨a,b⟩ ha
   rcases mem_union.mp ha with hOld|hNew
   · exact E.Eb (show S.NS⊆(S.FX C hC).NS from subset_union_left) hOld
   · obtain ⟨hD',hM,hu,hv⟩:=mem_filter.mp hNew
     rw [S.Aj E] at hu hv
     obtain ⟨u,hLocalU,hUA⟩:=mem_image.mp hu
     obtain ⟨v,hLocalV,hVB⟩:=mem_image.mp hv
     change E.toFun u=a at hUA
     change E.toFun v=b at hVB
     subst a
     subst b
     exact mem_image.mpr ⟨(u,v),mem_union_right _ (mem_filter.mpr ⟨(hEdges u hLocalU v hLocalV).mp hD',
       fun hm=>hM ((E.HS u v).mpr hm),hLocalU,hLocalV⟩),rfl⟩
end Be.Bi
namespace Be.Lp
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)}
   (E: wF G M H K) {r: Fin N} (R: Lp G M r)
lemma gM (L: SimpleGraph (Fin N)) (J: SimpleGraph (Fin P))
   (hL: L≤ G) (hJ: J≤ H)
   (hEdges:∀u∈R.tree.vertices,∀v∈R.tree.vertices,J.Adj (E.toFun u) (E.toFun v)↔ L.Adj u v):
   (R.z8 L hL).Nd E=(R.Nd E).z8 J hJ:= by
 apply Lp.Kd
 · dsimp only [z8,Lp.Nd]
   rw [Bi.uN]
   apply congrArg Bi.normalized
   apply R.tree.bT E
   intro u hu v hv
   simpa only [mem_filter,mem_univ,true_and] using hEdges u hu v hv
 · rfl
 · rfl
 · rfl
 · rfl
end Be.Lp
end
noncomputable section
namespace Be.Db
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)} {ell: ℕ}
   {E: wF G M H K} {S: tI G M ell}
   {T: tI H K ell} (F: Db E S T)
include F in
lemma DV
   (hReflect:∀u,u∉S.Nm→∀v,v∉S.Nm→ T.NV.Adj (E.toFun u) (E.toFun v)→ S.NV.Adj u v):
   G8.Mr E S.z9.ND T.z9.ND:= by
 intro r R hR
 change (S.ND.state r).map (fun R=>R.z8 S.NV S.MF)=some R at hR
 obtain ⟨Q,hQ,hQR⟩:=Option.map_eq_some_iff.mp hR
 change (T.ND.state (E.toFun r)).map (fun R=>R.z8 T.NV T.MF)=some (R.Nd E)
 rw [F.present r Q hQ,Option.map_some,←hQR]
 apply congrArg some
 apply Eq.symm
 apply Q.gM E S.NV T.NV S.MF T.MF
 intro u hu v hv
 exact ⟨hReflect u (S.k7 r Q hQ u hu) v (S.k7 r Q hQ v hv),F.NV u v⟩
end Be.Db
end
noncomputable section
namespace Be.IO
def Hf (D: IO) (ell: ℕ) (j: ℕ) (old: Ln): Ln:=
 if old.Nm then old else
   if hConsistent: D.history.JS then
     if hClosed: D.history.JX then
       match D.view ell with
       | none=>old
       | some U=>if h:∃u,D.history.identity u=j then
           { old with L8:=D.JD hConsistent hClosed U.z9 h.choose}
         else old
     else old
   else old
end IO
def rG (size ell: ℕ): Deterministic Unit Ln Ln:=
 C7.transform (C7.NE (collect Ln) size)
   (fun j z=>(z.leader j,z)) (fun j old NI=>IO.Hf NI ell j old)
lemma d3 (size ell: ℕ):(rG size ell).program.rounds ()=size:=rfl
end Be
noncomputable section
namespace Be
structure n9 where
 op:∀{N: ℕ} {G M: SimpleGraph (Fin N)} {r: Fin N},Lp G M r→ Lp G M r
 tree:∀{N: ℕ} {G M: SimpleGraph (Fin N)} {r: Fin N} (R: Lp G M r),(op R).tree=R.tree
 labelled:∀{N: ℕ} {G M: SimpleGraph (Fin N)} {r: Fin N} (R: Lp G M r)
   (ell: ℕ) (lab: Fin N ×Fin N→ ℕ),R.Mq ell lab→(op R).Mq ell lab
 map:∀{N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)}
   (E: wF G M H K) {r: Fin N} (R: Lp G M r),(op R).Nd E=op (R.Nd E)
namespace n9
variable (U: n9)
def model (A: tF): tF:=
 { A with state:=U.op A.state,complete:=by rw [U.tree A.state];exact A.complete}
def node (z: Ln): Ln:={z with L8:=z.L8.map U.model}
def phase {N ell: ℕ} {G M: SimpleGraph (Fin N)} (S: tI G M ell): tI G M ell:=
 S.mapRoots (fun _ R=>U.op R) (fun _ R=>congrArg Bi.vertices (U.tree R))
   (fun r R hR u v h=>S.I9 r R hR u v (by rw [U.tree R] at h;exact h))
   (fun r R h=>by rw [U.tree R];exact h) (fun _ R h=>U.labelled R ell S.labels h)
def program: Deterministic Unit Ln Ln:=C7.pointwise (fun _ z=>U.node z)
lemma Gb (A: tF):(U.model A).members=A.members:= by
 change (U.op A.state).tree.vertices.image A.history.identity=A.state.tree.vertices.image A.history.identity
 rw [U.tree A.state]
lemma At {N ell: ℕ} {G M: SimpleGraph (Fin N)} (A: tF)
   (S: tI G M ell) (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (out: Fin N→ Option ℕ) (hOut: ReportsMatching G ids out M)
   (hRep: A.Represents S ids hi out hOut):(U.model A).Represents (U.phase S) ids hi out hOut:= by
 obtain ⟨hAuth,hState⟩:=hRep
 refine ⟨hAuth,?_⟩
 let E:=A.history.embedding hAuth hi hOut A.KB
 change (S.ND.state (E.toFun A.root)).map (fun R=>U.op R)=some ((U.op A.state).Nd E)
 rw [hState,Option.map_some,U.map E A.state]
lemma encoding {N ell: ℕ} {G M: SimpleGraph (Fin N)} (S: tI G M ell)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (out: Fin N→ Option ℕ)
   (hOut: ReportsMatching G ids out M) (data: Fin N→ Ln)
   (h: Fi S ids hi out hOut data):
   Fi (U.phase S) ids hi out hOut (fun v=>U.node (data v)):= by
 refine ⟨h.neighbors,h.Jf,h.labels,h.Nm,h.NV,?_,?_,h.output⟩
 · intro v A hA
   obtain ⟨B,hB,hBA⟩:=Option.map_eq_some_iff.mp hA
   subst A
   obtain ⟨hRep,hMem⟩:=h.Jr v B hB
   exact ⟨U.At B S ids hi out hOut hRep,by rw [U.Gb];exact hMem⟩
 · intro r R hR
   change (S.ND.state r).map (fun R=>U.op R)=some R at hR
   obtain ⟨Q,hQ,hQR⟩:=Option.map_eq_some_iff.mp hR
   obtain ⟨A,hA⟩:=h.El r Q hQ
   refine ⟨U.model A,?_⟩
   intro v hv
   have hV: v∈Q.tree.vertices:=by rw [←hQR,U.tree] at hv;exact hv
   change (data v).L8.map U.model=some (U.model A)
   rw [hA v hV]
   rfl
def begin (limit: ℕ): n9 where
 op:=fun R=>R.IX limit
 tree:=fun _=>rfl
 labelled:=fun _ _ _ h=>h
 map:=by intro N P G M H K E r R;exact R.rS E limit
def hold (limit: ℕ): n9 where
 op:=fun R=>R.rC limit
 tree:=fun _=>rfl
 labelled:=fun _ _ _ h=>h
 map:=by intro N P G M H K E r R;exact R.c2 E limit
def backtrack: n9 where
 op:=fun R=>R.zS
 tree:=by intro N G M r R;unfold Lp.zS;split_ifs<;> rfl
 labelled:=fun R ell lab h=>R.eS ell lab h
 map:=by intro N P G M H K E r R;exact R.gL E
end n9
end Be
end
noncomputable section
namespace IL
section Family
variable {K I O: Type} (F: K→ Deterministic Unit I O)
abbrev IK:= Σ k: K,(F k).program.State
abbrev Fa:= Σ k: K,(F k).program.Msg
def unpack (k: K) (msg: Fa F): Option (F k).program.Msg:=
 if h: msg.1= k then some (h ▸msg.2) else none
lemma JN (k: K) (msg:(F k).program.Msg): unpack F k ⟨k,msg⟩= some msg:= by
 unfold unpack
 rw [dif_pos rfl]
def select: Deterministic K I O where
 program:={
   State:= IK F
   Msg:= Fa F
   rounds:= fun k=>(F k).program.rounds ()
   init:= fun k id inp _=>⟨k,(F k).program.init () id inp (fun _=> false)⟩
   send:= fun st=>⟨st.1,(F st.1).program.send st.2⟩
   step:= fun st msgs=>⟨st.1,(F st.1).program.step st.2 (msgs.filterMap (unpack F st.1))⟩
   out:= fun st=>(F st.1).program.out st.2}
 tape_independent:= by intros; rfl
lemma K4 {V: Type} [Fintype V] (H: SimpleGraph V) (k: K) (ids: V→ ℕ)
   (inp: V→ I) (t: ℕ):∀v,
   (select F).program.run H k ids inp (fun _ _=> false) t v=
     ⟨k,(F k).program.run H () ids inp (fun _ _=> false) t v⟩:= by
 induction t with
 | zero => intro v; rfl
 | succ t ih =>
   intro v
   rw [SmoothedMIS.LocalAlg.run]
   simp only [ih]
   change (⟨k,(F k).program.step ((F k).program.run H () ids inp (fun _ _=> false) t v)
     (((univ.filter (H.Adj v)).val.map (fun w=>
       (⟨k,(F k).program.send ((F k).program.run H () ids inp (fun _ _=> false) t w)⟩: Fa F))).filterMap (unpack F k))⟩: IK F)= _
   rw [Multiset.filterMap_map]
   simp only [Function.comp_def,JN]
   rw [show (fun x=> some ((F k).program.send ((F k).program.run H () ids inp (fun _ _=> false) t x)))=
     some ∘(fun x=>(F k).program.send ((F k).program.run H () ids inp (fun _ _=> false) t x)) from rfl,
     ←Multiset.filterMap_map,Multiset.filterMap_some]
   rfl
lemma GG {V: Type} [Fintype V] (H: SimpleGraph V) (k: K) (ids: V→ ℕ)
   (inp: V→ I) (v: V):
   (select F).program.output H k ids inp (fun _ _=> false) v=
     (F k).program.output H () ids inp (fun _ _=> false) v:= by
 unfold SmoothedMIS.LocalAlg.output
 change (select F).program.out ((select F).program.run H k ids inp (fun _ _=> false) ((F k).program.rounds ()) v)= _
 rw [K4]
 rfl
end Family
end IL
end
noncomputable section
namespace IM
variable {I: Type} (A: ℕ→ Deterministic Unit I I)
def MR: ℕ→ Deterministic Unit I I
 | 0 => C7.pointwise (fun _ inp=> inp)
 | n+1 => Ff.sequence (MR n) (A n) (fun _ _ _ out=> out)
def Dw {V: Type} [Fintype V] (H: SimpleGraph V) (ids: V→ ℕ) (inp: V→ I): ℕ→ V→ I
 | 0 => inp
 | n+1 => (A n).program.output H () ids (Dw H ids inp n) (fun _ _=> false)
lemma Gy {V: Type} [Fintype V] (H: SimpleGraph V) (ids: V→ ℕ) (inp: V→ I) (n: ℕ):∀v,
   (MR A n).program.output H () ids inp (fun _ _=> false) v= Dw A H ids inp n v:= by
 induction n with
 | zero => intro v; rfl
 | succ n ih =>
   intro v
   change (Ff.sequence (MR A n) (A n) (fun _ _ _ out=> out)).program.output H () ids inp (fun _ _=> false) v= _
   rw [Ff.CM]
   change (A n).program.output H () ids (fun v=>(MR A n).program.output H () ids inp (fun _ _=> false) v) (fun _ _=> false) v= _
   simp only [ih]
   rfl
lemma Gz (n: ℕ):(MR A n).program.rounds ()= n+∑t∈ range n,(A t).program.rounds ():= by
 induction n with
 | zero => rfl
 | succ n ih =>
   change (MR A n).program.rounds ()+1+(A n).program.rounds ()= _
   rw [ih,sum_range_succ]
   omega
end IM
end
noncomputable section
namespace Be
variable {K: Type}
def Mg (A B: Deterministic Unit Ln Ln): Deterministic Unit Ln Ln:=
 Ff.sequence A B (fun _ _ _ z=>z)
lemma A0 (A B: Deterministic Unit Ln Ln):
   (Mg A B).program.rounds ()=A.program.rounds ()+1+B.program.rounds ():=rfl
def AD (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   (size ell: ℕ) (mode: Bool) (count: ℕ): Deterministic Unit Ln Ln:=
 IM.MR (fun _=>x6 A k size ell mode) count
lemma jE (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   (size ell: ℕ) (mode: Bool) (count: ℕ):
   (AD A k size ell mode count).program.rounds ()=
     count*(5*size+7+(2*size+2)*A.program.rounds k):= by
 rw [AD,IM.Gz]
 simp only [gT,sum_const,card_range,smul_eq_mul]
 ring
def IC (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   (size ell: ℕ) (mode: Bool) (count: ℕ): Deterministic Unit Ln Ln:=
 Mg (if mode then rM size ell else C7.pointwise (fun _ z=>z))
   (Mg (AD A k size ell mode count) (yE size ell mode))
lemma s0 (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   (size ell: ℕ) (mode: Bool) (count: ℕ):
   (IC A k size ell mode count).program.rounds ()=
     count*(5*size+7+(2*size+2)*A.program.rounds k)+(if mode then size else 0)+size+4:= by
 unfold IC
 rw [A0,A0,jE,gY]
 cases mode<;> simp only [Bool.false_eq_true,if_false,if_true,d6]
 · change 0+1+_= _
   omega
 · omega
abbrev IJ:=ℕ ×ℕ ×ℕ
def oQ (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   (size ell limit: ℕ) (NP: IJ): Deterministic Unit Ln Ln:=
 Mg (n9.begin limit).program
   (Mg (IC A k size ell true NP.1)
     (Mg (n9.hold limit).program
       (Mg n9.backtrack.program
         (Mg (IC A k size ell false NP.2.1)
           (Mg (rG size ell) (IC A k size ell false NP.2.2))))))
lemma cV (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   (size ell limit: ℕ) (NP: IJ):
   (oQ A k size ell limit NP).program.rounds ()=
     (NP.1+NP.2.1+NP.2.2)*(5*size+7+(2*size+2)*A.program.rounds k)+5*size+18:= by
 simp only [oQ,A0,s0,d3,
   n9.program,C7.pointwise,Bool.false_eq_true,if_true,if_false]
 ring
def yJ (ell: ℕ): Deterministic Unit Ln Ln:=
 C7.pointwise (fun j z=>Ln.K8 ell j z.neighbors
   (if z.Nm then z.Md else z.Jf))
def If (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   (size ell limit bundles: ℕ) (NP: ℕ→ IJ): Deterministic Unit Ln Ln:=
 Mg (yJ ell) (IM.MR (fun t=>oQ A k size ell limit (NP t)) bundles)
lemma sF (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   (size ell limit bundles: ℕ) (NP: ℕ→ IJ):
   (If A k size ell limit bundles NP).program.rounds ()=
     1+bundles+∑t∈range bundles,
       (((NP t).1+(NP t).2.1+(NP t).2.2)*(5*size+7+(2*size+2)*A.program.rounds k)+5*size+18):= by
 rw [If,A0,IM.Gz]
 simp only [yJ,C7.pointwise,cV]
 omega
end Be
end
noncomputable section
namespace Be
lemma AZ (A B: Deterministic Unit Ln Ln)
   {N: ℕ} (G: SimpleGraph (Fin N)) (ids: Fin N→ ℕ) (data: Fin N→ Ln):
   execute (Mg A B) G () ids data=execute B G () ids (execute A G () ids data):= by
 funext v
 unfold execute Mg
 rw [Ff.CM]
end Be
end
noncomputable section
namespace Be.tE
variable {N s: ℕ} {G: SimpleGraph (Fin N)} (P: tE G s)
   {I: Type} (ids: Fin N→ ℕ) (hi: Function.Injective ids) (data: Fin N→ I)
include hi in
lemma Ex (u v: Fin N): ids v∈(P.NI ids data u).image Prod.fst↔ P.leader v=P.leader u:= by
 rw [NI,image_image]
 constructor
 · intro h
   obtain ⟨w,hw,hID⟩:=mem_image.mp h
   have hWV: w=v:=hi hID
   subst w
   exact (mem_filter.mp hw).2
 · intro h
   exact mem_image.mpr ⟨v,mem_filter.mpr ⟨mem_univ _,h⟩,rfl⟩
end Be.tE
namespace Be.G8
variable {N t: ℕ} {G M: SimpleGraph (Fin N)} (F: G8 G M)
   (P: tE G t) (hOwner:∀v,F.owner (P.leader v)=F.owner v)
include hOwner in
lemma dV (u v: Fin N) (hUV: P.leader u=P.leader v):
   F.BB P u=F.BB P v:= by
 have hO: F.owner u=F.owner v:=by rw [←hOwner u,←hOwner v,hUV]
 unfold BB
 rw [hO,hUV]
end Be.G8
namespace Be.tE
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
lemma w6 (hM: Matching G M) (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (u v: Fin N) (hUV: M.Adj u v):
   (Hv G M hM ids hi).leader u=(Hv G M hM ids hi).leader v:= by
 have hMate: Ni ids hi M u=v:=by
   unfold Ni
   rw [(tB.LW ids hi M (qJ.gP G M hM) u v).mpr hUV]
   rfl
 rw [q7,q7,←hMate]
 exact (k9 ids hi (Ni ids hi M)
   (vA ids hi M (qJ.gP G M hM)) u).symm
end Be.tE
namespace Be.tI
variable {N ell s: ℕ} {G M: SimpleGraph (Fin N)} (S: tI G M ell)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (hSize:∀r R,S.ND.state r=some R→ R.tree.vertices.card≤ s) (hS: 2≤ s)
lemma cY (u v: Fin N) (hUV: M.Adj u v):
   (S.tT ids hi hSize hS).leader u=(S.tT ids hi hSize hS).leader v:= by
 exact S.ND.dV _ (S.ND.t7 S.MG ids hi) u v
   (tE.w6 S.MG ids hi u v hUV)
lemma iR (r: Fin N) (R: Lp G M r) (hR: S.ND.state r=some R)
   (v: Fin N) (hV: v∈R.tree.vertices):(S.tT ids hi hSize hS).leader v=r:=
 S.ND.f8 _ r v ⟨R,hR,hV⟩
end Be.tI
end
noncomputable section
namespace Be.IO
variable {N s: ℕ} {G: SimpleGraph (Fin N)}
def Saturated (D: IO) (P: tE G s) (ids: Fin N→ ℕ): Prop:=
 ∀v,ids v∈D.keys→∀w,P.leader w=P.leader v→ ids w∈D.keys
lemma CK (D E: IO) (P: tE G s) (ids: Fin N→ ℕ)
   (hD: D.Saturated P ids) (hE: E.Saturated P ids):(D∪E: IO).Saturated P ids:= by
 intro v hv w hWV
 have hKeys:(D∪E: IO).keys=D.keys∪E.keys:=image_union D E
 rw [hKeys] at hv ⊢
 rcases mem_union.mp hv with hv|hv
 · exact mem_union_left _ (hD v hv w hWV)
 · exact mem_union_right _ (hE v hv w hWV)
lemma AF (P: tE G s) (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (data: Fin N→ Ln) (u: Fin N): Saturated (P.NI ids data u) P ids:= by
 intro v hv w hWV
 have hV:=(P.Ex ids hi data u v).mp hv
 exact (P.Ex ids hi data u w).mpr (hWV.trans hV)
variable {ell: ℕ} {M: SimpleGraph (Fin N)} (S: tI G M ell)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (hSize:∀r R,S.ND.state r=some R→ R.tree.vertices.card≤ s) (hS: 2≤ s)
   (D: IO) (hSat: D.Saturated (S.tT ids hi hSize hS) ids)
include hSat
lemma vV:∀v,ids v∈D.keys→∀w,M.Adj v w→ ids w∈D.keys:= by
 intro v hv w hVW
 exact hSat v hv w (S.cY ids hi hSize hS v w hVW).symm
lemma CL:∀v,ids v∈D.keys→∀r R,S.ND.state r=some R→ v∈R.tree.vertices→
   ∀w∈R.tree.vertices,ids w∈D.keys:= by
 intro v hv r R hR hV w hW
 exact hSat v hv w ((S.iR ids hi hSize hS r R hR w hW).trans
   (S.iR ids hi hSize hS r R hR v hV).symm)
lemma ER (out: Fin N→ Option ℕ) (hOut: ReportsMatching G ids out M)
   (data: Fin N→ Ln) (h: Fi S ids hi out hOut data)
   (hD:∀z∈D,∃v,z=(ids v,data v)):
   ∃(hClosed: D.history.JX)
     (U: tI D.history.graph D.history.MG ell),
     D.view ell=some U∧ Db (D.history.embedding (D.w7 h hD) hi hOut hClosed) U S:= by
 have hPair:=D.vV S ids hi hSize hS hSat
 have hWhole:=D.CL S ids hi hSize hS hSat
 have hClosed:=D.uB h hD hPair
 obtain ⟨U,hView,hEmbed⟩:=D.n6 h hD hClosed hPair hWhole
 exact ⟨hClosed,U,hView,hEmbed⟩
end Be.IO
end
noncomputable section
namespace Be
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)}
namespace wF
variable (E: wF G M H K)
lemma DT {A B: Finset (Fin N)} (h: Disjoint A B):
   Disjoint (A.image E.toFun) (B.image E.toFun):= by
 apply disjoint_left.mpr
 intro v hv hw
 obtain ⟨a,ha,hav⟩:=mem_image.mp hv
 obtain ⟨b,hb,hbv⟩:=mem_image.mp hw
 have hAB:=E.injective (hav.trans hbv.symm)
 exact disjoint_left.mp h ha (hAB.symm ▸hb)
end wF
namespace IQ
variable (F: wF G M H K) {alpha beta: Fin N}
   {A: Bi G M alpha} {B: Bi G M beta}
   {Q: v9 G M alpha} {k n: ℕ} {hn: n≤ Q.length}
   {C: Finset (Fin N ×Fin N)} (S: IQ A B Q k n hn C)
end IQ
end Be
end
noncomputable section
namespace Be
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)}
lemma cC {α: Type} [DecidableEq α] (A B C D X: Finset α)
   (hAB: Disjoint A B) (hCD: Disjoint C D) (hPart: A∪B=X) (hPart': C∪D=X)
   (hRight: B=D): A=C:= by
 subst D
 apply Subset.antisymm
 · intro v hv
   have hh: v∈C∪B:=by rw [hPart',←hPart];exact mem_union_left _ hv
   rcases mem_union.mp hh with hh|hh
   · exact hh
   · exact (disjoint_left.mp hAB hv hh).elim
 · intro v hv
   have hh: v∈A∪B:=by rw [hPart,←hPart'];exact mem_union_left _ hv
   rcases mem_union.mp hh with hh|hh
   · exact hh
   · exact (disjoint_left.mp hCD hv hh).elim
namespace G6
variable (E: wF G M H K) (hK: Matching H K) {alpha beta: Fin N}
   (D: G6 G M alpha beta)
lemma xG: D.remaining.Nd E=(D.Nd E hK).remaining:= by
 change (D.right.MT {D.target}).Nd E=(D.right.Nd E).MT {E.pairMap D.target}
 rw [D.right.Ai E]
 rfl
lemma cF:
   (D.Nd E hK).JM.vertices=D.JM.vertices.image E.toFun:= by
 have hRight:(D.Nd E hK).remaining.vertices=D.remaining.vertices.image E.toFun:=by
   rw [←D.xG E hK,D.remaining.Aj E]
 apply cC _ _ _ _
   ((D.left.vertices∪D.right.vertices).image E.toFun) (D.Nd E hK).p9
   (E.DT D.p9)
 · rw [(D.Nd E hK).v8]
   change (D.left.Nd E).vertices∪(D.right.Nd E).vertices=_
   rw [D.left.Aj E,D.right.Aj E,image_union]
 · rw [←image_union,D.v8]
 · exact hRight
lemma gN:
   ((D.remaining.FX D.KC D.HW).normalized).Nd E=
   (((D.Nd E hK).remaining.FX (D.Nd E hK).KC
     (D.Nd E hK).HW).normalized):= by
 have hC:∀u v,(u,v)∈E.Nc D.KC→ H.Adj u v:=by
   intro u v h
   apply (D.Nd E hK).HW u v
   rw [D.Ee E hK]
   exact h
 rw [(D.remaining.FX D.KC D.HW).uN E,
   D.remaining.m7 E D.KC D.HW hC]
 simp only [D.Ee E hK]
 congr 2
 exact D.xG E hK
lemma d9:
   ((D.JM.FX D.KC D.HW).normalized).Nd E=
   (((D.Nd E hK).JM.FX (D.Nd E hK).KC
     (D.Nd E hK).HW).normalized):= by
 have hC:∀u v,(u,v)∈E.Nc D.KC→ H.Adj u v:=by
   intro u v h
   change (u,v)∈D.KC.image E.pairMap at h
   obtain ⟨⟨a,b⟩,ha,hEq⟩:=mem_image.mp h
   obtain ⟨rfl,rfl⟩:=Prod.mk.inj hEq
   exact (E.LH a b).mpr (D.HW a b ha)
 rw [D.JM.FX D.KC D.HW|>.uN E,
   D.JM.m7 E D.KC D.HW hC]
 simp only [D.Ee E hK]
 apply Bi.oN _ _ hK
 · exact E.Eb D.En
 · have hSub:(D.Nd E hK).JM.NS ⊆(D.Nd E hK).KC:=
     (D.Nd E hK).En
   simpa only [D.Ee E hK] using hSub
 · rw [D.JM.Aj E,D.cF E hK]
end G6
end Be
end
noncomputable section
namespace Be.C2
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)}
   (E: wF G M H K) (hK: Matching H K) {alpha beta: Fin N}
   (D: C2 G M alpha beta)
def NO:=Classical.choice D.transfer
lemma uL:(D.Nd E hK).data.KC=E.Nc D.data.KC:=
 D.data.Ee E hK
lemma rU: D.NO.right.Nd E=(D.Nd E hK).NO.right:= by
 rw [D.NO.MT,(D.Nd E hK).NO.MT,D.data.right.Ai E]
 congr 1
 rw [D.HN E hK,D.path.xF E]
 rfl
lemma c4:
   (D.Nd E hK).NO.left.vertices=D.NO.left.vertices.image E.toFun:= by
 have hRight:(D.Nd E hK).NO.right.vertices=D.NO.right.vertices.image E.toFun:=by
   rw [←D.rU E hK,D.NO.right.Aj E]
 apply cC _ _ _ _
   ((D.data.left.vertices∪D.data.right.vertices).image E.toFun) (D.Nd E hK).NO.disjoint
   (E.DT D.NO.disjoint)
 · rw [(D.Nd E hK).NO.vertices]
   change (D.data.left.Nd E).vertices∪(D.data.right.Nd E).vertices=_
   rw [D.data.left.Aj E,D.data.right.Aj E,image_union]
 · rw [←image_union,D.NO.vertices]
 · exact hRight
lemma fF:
   ((D.NO.left.FX D.data.KC D.data.HW).normalized).Nd E=
   (((D.Nd E hK).NO.left.FX (D.Nd E hK).data.KC
     (D.Nd E hK).data.HW).normalized):= by
 have hC:∀u v,(u,v)∈E.Nc D.data.KC→ H.Adj u v:=by
   intro u v h
   apply (D.Nd E hK).data.HW u v
   rw [D.uL E hK]
   exact h
 rw [(D.NO.left.FX D.data.KC D.data.HW).uN E,
   D.NO.left.m7 E D.data.KC D.data.HW hC]
 simp only [D.uL E hK]
 apply Bi.oN _ _ hK
 · exact E.Eb D.NO.Jl
 · have hSub:(D.Nd E hK).NO.left.NS⊆(D.Nd E hK).data.KC:=
     (D.Nd E hK).NO.Jl
   simpa only [D.uL E hK] using hSub
 · rw [D.NO.left.Aj E,D.c4 E hK]
lemma d8:
   ((D.NO.right.FX D.data.KC D.data.HW).normalized).Nd E=
   (((D.Nd E hK).NO.right.FX (D.Nd E hK).data.KC
     (D.Nd E hK).data.HW).normalized):= by
 have hC:∀u v,(u,v)∈E.Nc D.data.KC→ H.Adj u v:=by
   intro u v h
   apply (D.Nd E hK).data.HW u v
   rw [D.uL E hK]
   exact h
 rw [(D.NO.right.FX D.data.KC D.data.HW).uN E,
   D.NO.right.m7 E D.data.KC D.data.HW hC]
 simp only [D.uL E hK]
 congr 2
 exact D.rU E hK
end Be.C2
end
noncomputable section
namespace Be.Db
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)} {ell: ℕ}
   {E: wF G M H K} {S: tI G M ell}
   {T: tI H K ell} (F: Db E S T)
include F
lemma Gw (v: Fin N) (hAlive: v∉S.Nm) (r: Fin P) (R: Lp H K r)
   (hR: T.ND.state r=some R) (hV: E.toFun v∈R.tree.vertices):
   ∃(s: Fin N) (U: Lp G M s),S.ND.state s=some U∧ E.toFun s=r∧ HEq (U.Nd E) R:= by
 have hOwner: T.ND.owner (E.toFun v)=some r:=(T.ND.KP r _).mpr ⟨R,hR,hV⟩
 rw [F.owner v hAlive] at hOwner
 obtain ⟨s,hS,hEq⟩:=Option.map_eq_some_iff.mp hOwner
 obtain ⟨U,hU,hVU⟩:=(S.ND.KP s v).mp hS
 refine ⟨s,U,hU,hEq,?_⟩
 subst r
 have hState: U.Nd E=R:=Option.some.inj ((F.present s U hU).symm.trans hR)
 exact heq_of_eq hState
lemma oE (x y: Fin N) (mode: Bool) (hLive: S.NV.Adj x y)
   (h: T.Bd (E.toFun x) (E.toFun y) mode): S.Bd x y mode:= by
 obtain ⟨R,hFlag⟩:=h
 rcases R with ⟨r,s,A,B,hA,hB,hDistinct,hX,hY,hBridge,hUnmatched,Q⟩
 obtain ⟨a,A',hA',hAR,hAA⟩:=F.Gw x (S.HK _ _ hLive).1 r A hA hX
 obtain ⟨b,B',hB',hBR,hBB⟩:=F.Gw y (S.HK _ _ hLive).2 s B hB hY
 subst r
 subst s
 cases eq_of_heq hAA
 cases eq_of_heq hBB
 have hXY:¬M.Adj x y:=fun hm=>hUnmatched ((E.HS _ _).mpr hm)
 have hLocalDistinct: a≠b:=fun hab=>hDistinct (congrArg E.toFun hab)
 have hXL: x∈A'.tree.vertices:=by
   rw [A'.Aj E] at hX
   obtain ⟨v,hv,hEq⟩:=mem_image.mp hX
   exact E.injective hEq ▸hv
 have hYL: y∈B'.tree.vertices:=by
   rw [B'.Aj E] at hY
   obtain ⟨v,hv,hEq⟩:=mem_image.mp hY
   exact E.injective hEq ▸hv
 let C:=A'.tree.Hj B'.tree x y
 have hQ: C3 (Mv H (E.Nc C)) K:=by
   have hMemory:=A'.tree.pA E B'.tree x y
   change C3 (Mv H ((A'.tree.Nd E).Hj (B'.tree.Nd E)
     (E.toFun x) (E.toFun y))) K at Q
   rw [hMemory] at Q
   exact Q
 let L:=hQ.MS (E.NH C) a (E.l8 C hQ)
 let R: qF S x y:=
   { ME:=a,L7:=b,left:=A',right:=B',HJ:=hA',GE:=hB',
     distinct:=hLocalDistinct,M1:=hXL,head_mem:=hYL,IY:=hLive,
     zV:=hXY,path:=L}
 exact ⟨⟨R,hFlag⟩⟩
end Be.Db
end
noncomputable section
namespace Be.Bb
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)} {ell: ℕ}
   {E: wF G M H K} {S: tI G M ell}
   {T: tI H K ell} (F: Db E S T)
   {x y: Fin N} {R: y7 S x y}
def Nd (A: Bb R): Bb (R.Nd F):= by
 cases A with
 | single hOwner =>
   apply Bb.single
   have hAlive:=(S.HK _ _ R.IY).2
   rw [F.owner y hAlive]
   rcases hOwner with hOwner|hOwner
   · exact Or.inl (by rw [hOwner];rfl)
   · exact Or.inr (by rw [hOwner];rfl)
 | inactive D B hB hAT hBT hStem hTarget hInactive =>
   refine Bb.inactive (G6.Nd E T.MG D) (B.Nd E)
     (F.present _ _ hB) ?_ ?_ ?_ ?_ ?_
   · exact congrArg (Bi.Nd E) hAT
   · exact congrArg (Bi.Nd E) hBT
   · exact congrArg (v9.Nd E) hStem
   · exact congrArg E.pairMap hTarget
   ·
     intro Q hQ i hi hEq
     change B.active.map (fun Q=>Q.Nd E)=some Q at hQ
     obtain ⟨L,hL,hLQ⟩:=Option.map_eq_some_iff.mp hQ
     rw [←hLQ] at hEq hi
     exact hInactive L hL i hi (E.x4 hEq)
 | active D B hB hAT hBT hStem hTarget hActive =>
   refine Bb.active (C2.Nd E T.MG D) (B.Nd E)
     (F.present _ _ hB) ?_ ?_ ?_ ?_ ?_
   · exact congrArg (Bi.Nd E) hAT
   · exact congrArg (Bi.Nd E) hBT
   · exact congrArg (v9.Nd E) hStem
   · exact congrArg E.pairMap hTarget
   · change B.active.map (fun Q=>Q.Nd E)=some (D.Ng.Nd E)
     rw [hActive]
     rfl
lemma xH (A: Bb R) (hNo:¬S.Bd x y true):
   Dd true (E.toFun x) (E.toFun y) T (A.Nd F).Nj:= by
 apply Dd.extension rfl (R.Nd F) _ (A.Nd F)
 exact fun h=>hNo (F.oE x y true R.IY h)
end Be.Bb
end
noncomputable section
namespace Be.v9
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)}
   (E: wF G M H K) {r: Fin N} (Q: v9 G M r)
lemma B3 (lab: Fin N ×Fin N→ ℕ) (lab': Fin P ×Fin P→ ℕ)
   (a: Fin N ×Fin N) (hLab: lab' (E.pairMap a)=lab a):
   (Q.Nd E).Nl lab' (E.pairMap a)=Q.Nl lab a:= by
 by_cases hArc:∃i,i< Q.length∧ Q.KA i=a
 · obtain ⟨i,hi,rfl⟩:=hArc
   rw [←Q.uK E i,(Q.Nd E).KX lab' i hi,Q.KX lab i hi]
   rw [Q.uK E i,hLab]
 · have hNo:¬∃i,i<(Q.Nd E).length∧(Q.Nd E).KA i=E.pairMap a:=by
     rintro ⟨i,hi,hEq⟩
     exact hArc ⟨i,hi,E.x4 hEq⟩
   rw [Nl,dif_neg hNo,Nl,dif_neg hArc,hLab]
end Be.v9
end
noncomputable section
namespace Be.Bb
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)} {ell: ℕ}
   {E: wF G M H K} {S: tI G M ell}
   {T: tI H K ell} (F: Db E S T)
   {x y: Fin N} {R: y7 S x y}
lemma sY (hOwner: S.ND.owner y=none∨ S.ND.owner y=some R.root):
   G8.Mr E (Bb.single (R:=R) hOwner).Nj.ND
     ((Bb.single (R:=R) hOwner).Nd F).Nj.ND:= by
 apply G8.Mr.update_one E F.present _ _ ?_ rfl rfl
 apply Lp.Kd
 · dsimp only [Lp.Nd]
   rw [Bi.uN]
   apply congrArg Bi.normalized
   apply Bi.FJ
   change E.Nc (R.state.tree.NS∪{(R.NX.vertex (2*R.NX.length),y),
     (y,R.NX.vertex (2*R.NX.length)),(y,R.NW)})=
     E.Nc R.state.tree.NS∪{(E.toFun (R.NX.vertex (2*R.NX.length)),E.toFun y),
       (E.toFun y,E.toFun (R.NX.vertex (2*R.NX.length))),(E.toFun y,E.toFun R.NW)}
   simp only [wF.Nc,image_union,image_insert,image_singleton]
   rfl
 · apply congrArg some
   apply v9.Kd
   · rfl
   · funext i
     exact (R.NX.o9 E y R.NW i).symm
 · rfl
 · rfl
 · rfl
lemma mV {beta: Fin N} (D: G6 G M R.root beta)
   (B: Lp G M beta) (hB: S.ND.state beta=some B)
   (hAT: R.state.tree=D.left) (hBT: B.tree=D.right)
   (hStem: D.NX=R.NX) (hTarget: D.target=(y,R.NW))
   (hInactive:∀Q,B.active=some Q→∀i,i< Q.length→ Q.KA i≠D.target):
   let A:=Bb.inactive D B hB hAT hBT hStem hTarget hInactive
   G8.Mr E A.Nj.ND (A.Nd F).Nj.ND:= by
 dsimp only
 apply G8.Mr.Le E F.present D.distinct _ _ _ _ ?_ ?_ rfl rfl
 · apply Lp.Kd
   · exact D.d9 E T.MG
   · apply congrArg some
     apply v9.Kd
     · rfl
     · funext i
       exact (D.NX.o9 E D.target.1 D.target.2 i).symm
   · rfl
   · rfl
   · rfl
 · apply Lp.Kd
   · exact D.gN E T.MG
   · rfl
   · rfl
   · rfl
   · rfl
lemma qN {beta: Fin N} (D: C2 G M R.root beta)
   (B: Lp G M beta) (hB: S.ND.state beta=some B)
   (hAT: R.state.tree=D.data.left) (hBT: B.tree=D.data.right)
   (hStem: D.data.NX=R.NX) (hTarget: D.data.target=(y,R.NW))
   (hActive: B.active=some D.Ng):
   let A:=Bb.active D B hB hAT hBT hStem hTarget hActive
   G8.Mr E A.Nj.ND (A.Nd F).Nj.ND:= by
 dsimp only
 apply G8.Mr.Le E F.present D.data.distinct _ _ _ _ ?_ ?_ rfl rfl
 · apply Lp.Kd
   · exact D.fF E T.MG
   · exact congrArg some (D.HN E T.MG).symm
   · rfl
   · rfl
   · rfl
 · apply Lp.Kd
   · exact D.d8 E T.MG
   · apply congrArg some
     exact D.Ng.HO E _ _
   · rfl
   · rfl
   · rfl
lemma Ie (A: Bb R):
   G8.Mr E A.Nj.ND (A.Nd F).Nj.ND:= by
 cases A with
 | single hOwner => exact sY F hOwner
 | inactive D B hB hAT hBT hStem hTarget hInactive => exact mV F D B hB hAT hBT hStem hTarget hInactive
 | active D B hB hAT hBT hStem hTarget hActive => exact qN F D B hB hAT hBT hStem hTarget hActive
lemma Ju (A: Bb R):(A.Nd F).Nf=A.Nf.Nd E:= by
 cases A with
 | single hOwner =>
   apply v9.Kd
   · rfl
   · funext i
     exact R.NX.o9 E y R.NW i
 | inactive D B hB hAT hBT hStem hTarget hInactive =>
   apply v9.Kd
   · rfl
   · funext i
     exact D.NX.o9 E D.target.1 D.target.2 i
 | active D B hB hAT hBT hStem hTarget hActive => exact D.HN E T.MG
lemma vC (A: Bb R) (a: Fin N ×Fin N) (hA: a.1∉S.Nm):
   (A.Nd F).Nj.labels (E.pairMap a)=A.Nj.labels a:= by
 rw [(A.Nd F).LO,A.LO,A.Ju F]
 exact A.Nf.B3 E S.labels T.labels a (F.labels a hA)
end Be.Bb
end
noncomputable section
namespace Be.qF
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)} {ell: ℕ}
   {E: wF G M H K} {S: tI G M ell}
   {T: tI H K ell} (F: Db E S T)
   {x y: Fin N} (R: qF S x y)
lemma Ie: G8.Mr E (S.sE R).ND
   (T.sE (R.Nd F)).ND:= by
 intro r A hA
 change (if r∈({R.ME,R.L7}: Finset (Fin N)) then none else S.ND.state r)=some A at hA
 change (if E.toFun r∈({E.toFun R.ME,E.toFun R.L7}: Finset (Fin P)) then none
   else T.ND.state (E.toFun r))=some (A.Nd E)
 split_ifs at hA with hRemoved
 have hNot: E.toFun r∉({E.toFun R.ME,E.toFun R.L7}: Finset (Fin P)):=by
   simpa only [mem_insert,mem_singleton,E.injective.eq_iff] using hRemoved
 rw [if_neg hNot]
 exact F.present r A hA
lemma JA (u: Fin N) (hU: u∉S.Nm) (hPhys: E.toFun u∉T.Nm):
   u∈(S.sE R).Nm↔ E.toFun u∈(T.sE (R.Nd F)).Nm:= by
 change u∈S.Nm∪(R.left.tree.vertices∪R.right.tree.vertices)↔
   E.toFun u∈T.Nm∪((R.left.Nd E).tree.vertices∪(R.right.Nd E).tree.vertices)
 rw [R.left.Aj E,R.right.Aj E]
 simp only [mem_union,hU,hPhys,false_or]
 constructor
 · exact Or.imp (fun h=>mem_image.mpr ⟨u,h,rfl⟩) (fun h=>mem_image.mpr ⟨u,h,rfl⟩)
 · intro h
   rcases h with h|h
   · obtain ⟨v,hv,hEq⟩:=mem_image.mp h
     exact Or.inl (E.injective hEq ▸hv)
   · obtain ⟨v,hv,hEq⟩:=mem_image.mp h
     exact Or.inr (E.injective hEq ▸hv)
end Be.qF
end
noncomputable section
namespace Be.IO.NR
variable {D: IO} {ell: ℕ} {S: tI D.history.graph D.history.MG ell}
   {N: ℕ} {G M: SimpleGraph (Fin N)} {T: tI G M ell}
   {E: wF D.history.graph D.history.MG G M}
   (F: Db E S T) {mode: Bool} {u v: Fin D.history.keys.card}
def LT (W: NR S mode u v): tI G M ell:=
 match W with
 | augmentation R _ => T.sE (R.Nd F)
 | extension _ _ _ A => (A.Nd F).Nj
lemma Ef (W: NR S mode u v): Dd mode (E.toFun u) (E.toFun v) T (W.LT F):= by
 cases W with
 | augmentation R hFlag => exact Dd.augmentation (R.Nd F) hFlag
 | extension hMode R hNo A =>
   subst mode
   exact A.xH F hNo
lemma Kz (W: NR S mode u v): G8.Mr E W.result.ND (W.LT F).ND:= by
 cases W with
 | augmentation R hFlag => exact R.Ie F
 | extension hMode R hNo A => exact A.Ie F
end Be.IO.NR
end
noncomputable section
namespace Be.Db
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)} {ell: ℕ}
   {E: wF G M H K} {S: tI G M ell}
   {T: tI H K ell} (F: Db E S T)
include F in
lemma w2 (x y: Fin N) (hLive: S.NV.Adj x y)
   (R: y7 T (E.toFun x) (E.toFun y)): Nonempty (y7 S x y):= by
 rcases R with ⟨r,A,hA,P,hP,Q,hExt,hInside,hLabel,hEnd,hHeld,hExtended,hBound,w,hMatched,hFreshY,hFreshW,hEligible,hBridge,hUnmatch⟩
 have hX: E.toFun x∈A.tree.vertices:=by
   rw [←hEnd]
   exact A.tree.EA Q hInside (Q.mem_support (2*Q.length) le_rfl)
 obtain ⟨a,A',hA',hAR,hAA⟩:=F.Gw x (S.HK _ _ hLive).1 r A hA hX
 subst r
 cases eq_of_heq hAA
 obtain ⟨b,hBW⟩:=E.B7 y w hMatched
 subst w
 have hMate: M.Adj y b:=(E.HS y b).mp hMatched
 have hRange:=Q.HC E A'.tree.NS hInside
 let L:=Q.MS E a hRange
 have hLI: L.Nv A'.tree.NS:=Q.Ct E a hRange A'.tree.NS hInside
 have hPE: A'.active.map (fun P=>P.Nd E)=some P:=hP
 obtain ⟨P',hP',hPP⟩:=Option.map_eq_some_iff.mp hPE
 have hPL: P'.length=P.length:=congrArg (fun (Q: v9 H K (E.toFun a))=>Q.length) hPP
 have hPQ: P'.M4 L:=by
   refine ⟨by change P'.length≤ Q.length;rw [hPL];exact hExt.1,?_⟩
   intro i hi
   apply E.injective
   have hPi: E.toFun (P'.vertex i)=P.vertex i:=congrArg (fun (Q: v9 H K (E.toFun a))=>Q.vertex i) hPP
   change i≤ 2*P'.length at hi
   have hiP: i≤ 2*P.length:=by rw [←hPL];exact hi
   have hLen: P.length≤ Q.length:=hExt.1
   have hQi:=Q.Cu E a hRange i (by omega)
   change E.toFun (L.vertex i)=Q.vertex i at hQi
   exact hQi.trans ((hExt.2 i hiP).trans hPi.symm)
 have hLLabel: L.Mq ell S.labels:=by
   refine ⟨hLabel.1,?_⟩
   intro i hi
   change i< Q.length at hi
   have hAlive:(L.KA i).1∉S.Nm:=S.k7 a A' hA' _
     (A'.tree.EA L hLI (L.mem_support (2*i+1) (by change 2*i+1≤ 2*Q.length;omega)))
   change S.labels (L.KA i)≤ i+1
   rw [←F.labels _ hAlive,Q.sK E a hRange i hi]
   exact hLabel.2 i hi
 have hFresh (v: Fin N) (hOld: E.toFun v∉Q.support): v∉L.support:=by
   intro hv
   obtain ⟨i,hi,hIV⟩:=mem_image.mp hv
   have hi': i≤ 2*Q.length:=by have hI:=mem_range.mp hi;change i< 2*Q.length+1 at hI;omega
   have hPhys:=Q.Cu E a hRange i hi'
   change E.toFun (L.vertex i)=Q.vertex i at hPhys
   have hEq: Q.vertex i=E.toFun v:=hPhys.symm.trans (congrArg E.toFun hIV)
   exact hOld (hEq ▸Q.mem_support i hi')
 refine ⟨{
   root:=a
   state:=A'
   present:=hA'
   J5:=P'
   Lq:=hP'
   NX:=L
   DL:=hPQ
   inside:=hLI
   labelled:=hLLabel
   NC:=?_
   MK:=hHeld
   H9:=hExtended
   bound:=hBound
   NW:=b
   matched:=hMate
   Kq:=hFresh y hFreshY
   Kp:=hFresh b hFreshW
   My:=?_
   IY:=hLive
   zV:=fun hm=>hUnmatch ((E.HS x y).mpr hm)}⟩
 · apply E.injective
   exact (Q.Cu E a hRange (2*Q.length) le_rfl).trans hEnd
 · rw [←F.labels (y,b) (S.HK _ _ hLive).2]
   exact hEligible
end Be.Db
end
noncomputable section
namespace Be.IO
variable {N ell s: ℕ} {G M: SimpleGraph (Fin N)} (S: tI G M ell)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (hSize:∀r R,S.ND.state r=some R→ R.tree.vertices.card≤ s) (hS: 2≤ s)
   (out: Fin N→ Option ℕ) (hOut: ReportsMatching G ids out M)
   (data: Fin N→ Ln) (h: Fi S ids hi out hOut data)
   (D: IO) (hD:∀z∈D,∃v,z=(ids v,data v))
   (hSat: D.Saturated (S.tT ids hi hSize hS) ids)
lemma GY (hClosed: D.history.JX) (v: Fin N) (hKey: ids v∈D.keys):
   ∃u: Fin D.history.keys.card,
     (D.history.embedding (D.w7 h hD) hi hOut hClosed).toFun u=v∧ D.history.identity u=ids v:= by
 obtain ⟨u,hU⟩:=D.history.rF (ids v) (D.rP hKey)
 refine ⟨u,?_,hU⟩
 apply hi
 exact (D.history.yA (D.w7 h hD) u).trans hU
include h hD hSat
end Be.IO
end
noncomputable section
namespace Be
variable {N: ℕ}
lemma nS (H: SimpleGraph (Fin N)):
   ∃D: Finset (Fin N),D.card≤ 2*optimum H∧
     ∀u v,H.Adj u v→ u∈ D∨ v∈ D:= by
 obtain ⟨E,hE,hCard⟩:= wA.Al H
 let D: Finset (Fin N):= E.biUnion (fun e=> e.val.toFinset)
 refine ⟨D,?_,?_⟩
 · calc
     D.card≤∑e∈ E,e.val.toFinset.card:= card_biUnion_le
     _≤∑_∈ E,(2:ℕ):= sum_le_sum (fun e _=> by
       rw [Sym2.card_toFinset];split_ifs<;> omega)
     _= 2*optimum H:= by simp [hCard,mul_comm]
 · intro u v huv
   obtain ⟨f,hf,w,hw,hf'⟩:= wA.Eh H E hE hCard
     ⟨s(u,v),H.mem_edgeSet.mpr huv⟩
   have hwD: w∈ D:= mem_biUnion.mpr ⟨f,hf,Sym2.mem_toFinset.mpr hf'⟩
   rcases Sym2.mem_iff.mp hw with hw|hw
   · exact Or.inl (hw ▸hwD)
   · exact Or.inr (hw ▸hwD)
namespace tE
variable {G: SimpleGraph (Fin N)} {s: ℕ} (P: tE G s)
def FE (D: Finset (Fin N)): Finset (Fin N):=
 univ.filter (fun v=> P.leader v∈ D)
lemma xN (D: Finset (Fin N)) (v: Fin N):
   v∈ P.FE D↔ P.leader v∈ D:= by simp [FE]
lemma tU (D: Finset (Fin N)):(P.FE D).card≤ s*D.card:= by
 have hSub: P.FE D ⊆D.biUnion (fun r=> univ.filter (fun v=> P.leader v=r)):= by
   intro v hv
   exact mem_biUnion.mpr ⟨P.leader v,(P.xN D v).mp hv,
     mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
 have hEach (r: Fin N):(univ.filter (fun v=> P.leader v=r)).card≤ s:= by
   by_cases hr: P.leader r=r
   · simpa only [hr] using P.small r
   · have hEmpty:(univ.filter (fun v=> P.leader v=r))=∅:= by
       apply eq_empty_iff_forall_notMem.mpr
       intro v hv
       have he:=(mem_filter.mp hv).2
       exact hr (by simpa only [he] using P.fixed v)
     rw [hEmpty,card_empty];omega
 calc
   _≤(D.biUnion (fun r=> univ.filter (fun v=> P.leader v=r))).card:= card_le_card hSub
   _≤∑r∈ D,(univ.filter (fun v=> P.leader v=r)).card:= card_biUnion_le
   _≤∑_∈ D,s:= sum_le_sum (fun r _=> hEach r)
   _= _:= by simp [mul_comm]
lemma oW (D: Finset (Fin N)) (u v: Fin N) (h: P.leader u=P.leader v):
   u∈ P.FE D↔ v∈ P.FE D:= by
 simp only [xN,h]
end tE
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
namespace tI
def tA (S: tI G M ell) (u v: Fin N): Prop:=
 ∃(r s: Fin N) (A: Lp G M r) (B: Lp G M s),
   r≠s∧ S.ND.state r=some A∧ S.ND.state s=some B∧
   u∈A.tree.vertices∧ v∈B.tree.vertices∧ S.NV.Adj u v∧¬M.Adj u v∧
   Nonempty (C3 (Mv G ((A.tree.NS∪B.tree.NS)∪{(u,v)})) M)
def dJ (S: tI G M ell) (u v: Fin N): Prop:=
 S.tA u v∨ S.tA v u
end tI
end Be
end
noncomputable section
namespace Be.tI
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
def l9 (S: tI G M ell): Finset (Sym2 (Fin N)):=
 (univ.filter (fun e: Fin N ×Fin N=> S.tA e.1 e.2)).image
   (fun e=> s(e.1,e.2))
lemma fG (S: tI G M ell) (u v: Fin N):
   s(u,v)∈S.l9↔ S.dJ u v:= by
 constructor
 · intro h
   obtain ⟨⟨a,b⟩,hab,he⟩:=mem_image.mp h
   have hBridge:=(mem_filter.mp hab).2
   rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
   · exact Or.inl hBridge
   · exact Or.inr hBridge
 · intro h
   rcases h with h|h
   · exact mem_image.mpr ⟨(u,v),mem_filter.mpr ⟨mem_univ _,h⟩,rfl⟩
   · exact mem_image.mpr ⟨(v,u),mem_filter.mpr ⟨mem_univ _,h⟩,Sym2.eq_swap⟩
lemma bA (S: tI G M ell):
   ∀u v,M.Adj u v→ s(u,v)∉S.l9:= by
 intro u v hM hE
 rcases (S.fG u v).mp hE with h|h
 · obtain ⟨r,s,A,B,_,_,_,_,_,_,hNot,_⟩:=h
   exact hNot hM
 · obtain ⟨r,s,A,B,_,_,_,_,_,_,hNot,_⟩:=h
   exact hNot hM.symm
lemma aW (S: tI G M ell)
   {r: Fin N} (R: Lp G M r) (hR: S.ND.state r=some R)
   (u v: Fin N) (hu: u∈R.tree.vertices) (hv: v∈R.tree.vertices):
   s(u,v)∉S.l9:= by
 intro hE
 have hBad:∀u v,u∈R.tree.vertices→ v∈R.tree.vertices→¬S.tA u v:= by
   intro a b ha hb h
   obtain ⟨s,t,A,B,hNe,hA,hB,ha',hb',_⟩:=h
   have hsr:=S.ND.BE s r a ⟨A,hA,ha'⟩ ⟨R,hR,ha⟩
   have htr:=S.ND.BE t r b ⟨B,hB,hb'⟩ ⟨R,hR,hb⟩
   exact hNe (hsr.trans htr.symm)
 rcases (S.fG u v).mp hE with h|h
 · exact hBad u v hu hv h
 · exact hBad v u hv hu h
lemma b6 (S: tI G M ell):
   ∀r R,S.ND.state r=some R→∀u v,(u,v)∈R.tree.NS→ s(u,v)∉S.l9:= by
 intro r R hR u v hArc
 have hEnds:=R.tree.Ft u v hArc
 exact S.aW R hR u v hEnds.1 hEnds.2
def vL (S: tI G M ell): tI G M ell:=
 S.DH S.l9 S.bA S.b6
lemma dB (S: tI G M ell):
   S.vL.ND.n8 S.vL.NV:= by
 intro r s hNe A B hA hB u v hLive hu hv hNotM hAug
 have hCand: S.dJ u v:=
   Or.inl ⟨r,s,A,B,hNe,hA,hB,hu,hv,hLive.1,hNotM,hAug⟩
 exact hLive.2 ((S.fG u v).mpr hCand)
end Be.tI
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
namespace y7
def unerase {S: tI G M ell} (E: Finset (Sym2 (Fin N)))
   (hM:∀u v,M.Adj u v→ s(u,v)∉E)
   (hMemory:∀r R,S.ND.state r=some R→∀u v,(u,v)∈R.tree.NS→ s(u,v)∉E)
   {x y: Fin N} (R: y7 (S.DH E hM hMemory) x y): y7 S x y:=
 { R with IY:= R.IY.1}
end y7
namespace tI
def wD (S: tI G M ell) (u v: Fin N): Prop:=
 ∃R: y7 S u v,¬S.ND.Mm R.root v
def tZ (S: tI G M ell): Finset (Sym2 (Fin N)):=
 (univ.filter (fun e: Fin N ×Fin N=> S.wD e.1 e.2)).image (fun e=>s(e.1,e.2))
lemma kY (S: tI G M ell) (u v: Fin N):
   s(u,v)∈S.tZ↔ S.wD u v∨ S.wD v u:= by
 constructor
 · intro h
   obtain ⟨⟨a,b⟩,hab,he⟩:=mem_image.mp h
   have hBridge:=(mem_filter.mp hab).2
   rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
   · exact Or.inl hBridge
   · exact Or.inr hBridge
 · intro h
   rcases h with h|h
   · exact mem_image.mpr ⟨(u,v),mem_filter.mpr ⟨mem_univ _,h⟩,rfl⟩
   · exact mem_image.mpr ⟨(v,u),mem_filter.mpr ⟨mem_univ _,h⟩,Sym2.eq_swap⟩
lemma cB (S: tI G M ell):
   ∀u v,M.Adj u v→ s(u,v)∉S.tZ:= by
 intro u v hM hE
 rcases (S.kY u v).mp hE with ⟨R,_⟩|⟨R,_⟩
 · exact R.zV hM
 · exact R.zV hM.symm
lemma bG (S: tI G M ell)
   {r: Fin N} (A: Lp G M r) (hA: S.ND.state r=some A)
   (u v: Fin N) (hu: u∈A.tree.vertices) (hv: v∈A.tree.vertices):
   s(u,v)∉S.tZ:= by
 intro hE
 have hBad:∀a b,a∈A.tree.vertices→ b∈A.tree.vertices→¬S.wD a b:= by
   intro a b ha hb ⟨R,hExternal⟩
   have hRoot:=S.ND.BE R.root r a ⟨R.state,R.present,R.K5⟩ ⟨A,hA,ha⟩
   apply hExternal
   rw [hRoot]
   exact ⟨A,hA,hb⟩
 rcases (S.kY u v).mp hE with h|h
 · exact hBad u v hu hv h
 · exact hBad v u hv hu h
lemma e1 (S: tI G M ell):
   ∀r R,S.ND.state r=some R→∀u v,(u,v)∈R.tree.NS→ s(u,v)∉S.tZ:= by
 intro r R hR u v hArc
 have hEnds:=R.tree.Ft u v hArc
 exact S.bG R hR u v hEnds.1 hEnds.2
def Cs (S: tI G M ell): tI G M ell:=
 S.DH S.tZ S.cB S.e1
lemma eF (S: tI G M ell)
   (hInternal:∀x y (R: y7 S x y),R.state.modified=false→
     S.ND.Mm R.root y→ False)
   (x y: Fin N) (R: y7 S.Cs x y) (hMod: R.state.modified=false): False:= by
 let Q:=R.unerase S.tZ S.cB S.e1
 by_cases hOwn: S.ND.Mm Q.root y
 · exact hInternal x y Q hMod hOwn
 · have hE: s(x,y)∈S.tZ:=(S.kY x y).mpr (Or.inl ⟨Q,hOwn⟩)
   exact R.IY.2 hE
end tI
end Be
end
noncomputable section
namespace Be.IO
variable {N ell size: ℕ} {G M: SimpleGraph (Fin N)} (S: tI G M ell)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (hSize:∀r V,S.ND.state r=some V→ V.tree.vertices.card≤ size) (hS: 2≤ size)
   (out: Fin N→ Option ℕ) (hOut: ReportsMatching G ids out M)
   (data: Fin N→ Ln) (h: Fi S ids hi out hOut data)
   (D: IO) (hD:∀z∈D,∃v,z=(ids v,data v))
   (hSat: D.Saturated (S.tT ids hi hSize hS) ids)
include h hD hSat in
lemma Ia (mode: Bool) (x y: Fin N) (hX: ids x∈D.keys) (hY: ids y∈D.keys):
   D.omission ell mode (ids x) (ids y)↔
     (S.tT ids hi hSize hS).leader x≠(S.tT ids hi hSize hS).leader y∧
     (if mode then Nonempty (y7 S x y)∨ Nonempty (y7 S y x)
       else S.Bd x y false∨ S.Bd y x false):= by
 obtain ⟨hClosed,U,hView,F⟩:=D.ER S ids hi hSize hS hSat out hOut data h hD
 let E:=D.history.embedding (D.w7 h hD) hi hOut hClosed
 obtain ⟨a,hAX,hA⟩:=GY S ids hi out hOut data h D hD hClosed x hX
 obtain ⟨b,hBY,hB⟩:=GY S ids hi out hOut data h D hD hClosed y hY
 change E.toFun a=x at hAX
 change E.toFun b=y at hBY
 have hExt (u v: Fin D.history.keys.card) (hLive: U.NV.Adj u v):
     Nonempty (y7 U u v)↔ Nonempty (y7 S (E.toFun u) (E.toFun v)):=by
   exact ⟨fun ⟨R⟩=>⟨R.Nd F⟩,fun hh=>F.w2 u v hLive hh.some⟩
 have hAug (u v: Fin D.history.keys.card) (hLive: U.NV.Adj u v):
     U.Bd u v false↔ S.Bd (E.toFun u) (E.toFun v) false:=by
   constructor
   · rintro ⟨R,hFlag⟩
     exact ⟨R.Nd F,fun hh=>Bool.noConfusion hh⟩
   · exact F.oE u v false hLive
 have hCross:(D.node (ids x)).leader (ids x)≠(D.node (ids y)).leader (ids y)↔
     (S.tT ids hi hSize hS).leader x≠(S.tT ids hi hSize hS).leader y:=by
   rw [D.Jw h hD x hX,D.Jw h hD y hY,h.Gr hSize hS x,h.Gr hSize hS y]
   exact hi.ne_iff
 constructor
 · rintro ⟨V,hV,u,v,hU,hVId,hDifferent,hRequest⟩
   have hVU: V=U:=Option.some.inj (hV.symm.trans hView)
   subst V
   have hua: u=a:=D.history.identity_injective (hU.trans hA.symm)
   have hvb: v=b:=D.history.identity_injective (hVId.trans hB.symm)
   subst u
   subst v
   refine ⟨hCross.mp hDifferent,?_⟩
   cases mode with
   | true =>
     change Nonempty (y7 U a b)∨ Nonempty (y7 U b a) at hRequest
     change Nonempty (y7 S x y)∨ Nonempty (y7 S y x)
     rcases hRequest with hReq|hReq
     · obtain ⟨R⟩:=hReq
       have hh: y7 S (E.toFun a) (E.toFun b):=R.Nd F
       rw [hAX,hBY] at hh
       exact Or.inl ⟨hh⟩
     · obtain ⟨R⟩:=hReq
       have hh: y7 S (E.toFun b) (E.toFun a):=R.Nd F
       rw [hAX,hBY] at hh
       exact Or.inr ⟨hh⟩
   | false =>
     change U.Bd a b false∨ U.Bd b a false at hRequest
     change S.Bd x y false∨ S.Bd y x false
     rcases hRequest with ⟨R,hFlag⟩|⟨R,hFlag⟩
     · have hh: qF S (E.toFun a) (E.toFun b):=R.Nd F
       rw [hAX,hBY] at hh
       exact Or.inl ⟨hh,fun hh=>Bool.noConfusion hh⟩
     · have hh: qF S (E.toFun b) (E.toFun a):=R.Nd F
       rw [hAX,hBY] at hh
       exact Or.inr ⟨hh,fun hh=>Bool.noConfusion hh⟩
 · rintro ⟨hDifferent,hRequest⟩
   have hLive: S.NV.Adj x y:=by
     cases mode with
     | true =>
       change Nonempty (y7 S x y)∨ Nonempty (y7 S y x) at hRequest
       rcases hRequest with hReq|hReq
       · exact hReq.some.IY
       · exact hReq.some.IY.symm
     | false => rcases hRequest with ⟨R,hFlag⟩|⟨R,hFlag⟩;exact R.IY;exact R.IY.symm
   have hLocalLive: U.NV.Adj a b:=by
     rw [(D.Lf ell U hView).NV]
     apply (D.F6 h hD hClosed a b).mpr
     refine ⟨?_,?_,?_⟩
     · apply (D.Ls h hD hClosed a).mpr
       exact ⟨hA.symm ▸hX,hAX.symm ▸(S.HK x y hLive).1⟩
     · apply (D.Ls h hD hClosed b).mpr
       exact ⟨hB.symm ▸hY,hBY.symm ▸(S.HK x y hLive).2⟩
     · change S.NV.Adj (E.toFun a) (E.toFun b)
       rw [hAX,hBY]
       exact hLive
   refine ⟨U,hView,a,b,hA,hB,hCross.mpr hDifferent,?_⟩
   cases mode with
   | true =>
     change Nonempty (y7 S x y)∨ Nonempty (y7 S y x) at hRequest
     change Nonempty (y7 U a b)∨ Nonempty (y7 U b a)
     rw [hExt a b hLocalLive,hExt b a hLocalLive.symm,hAX,hBY]
     exact hRequest
   | false =>
     change S.Bd x y false∨ S.Bd y x false at hRequest
     change U.Bd a b false∨ U.Bd b a false
     rw [hAug a b hLocalLive,hAug b a hLocalLive.symm,hAX,hBY]
     exact hRequest
end Be.IO
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell size: ℕ}
lemma Bs {r s: Fin N} (A: Bi G M r) (B: Bi G M s)
   (x y: Fin N): Mv G (A.Hj B x y)=Mv G ((A.NS∪B.NS)∪{(x,y)}):= by
 ext u v
 simp only [Mv,Bi.Hj,mem_union,mem_insert,mem_singleton,
   Prod.mk.injEq]
 tauto
namespace tI
variable (S: tI G M ell)
lemma kH (u v: Fin N): S.Bd u v false↔ S.tA u v:= by
 constructor
 · rintro ⟨R,hFlag⟩
   refine ⟨R.ME,R.L7,R.left,R.right,R.distinct,R.HJ,R.GE,
     R.M1,R.head_mem,R.IY,R.zV,?_⟩
   rw [←Bs]
   exact ⟨R.path⟩
 · rintro ⟨r,s,A,B,hNe,hA,hB,hu,hv,hLive,hUnmatched,⟨P⟩⟩
   have hPath: C3 (Mv G (A.tree.Hj B.tree u v)) M:=by
     rw [Bs]
     exact P
   exact ⟨⟨r,s,A,B,hA,hB,hNe,hu,hv,hLive,hUnmatched,hPath⟩,fun hh=>Bool.noConfusion hh⟩
variable (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (hSize:∀r V,S.ND.state r=some V→ V.tree.vertices.card≤ size) (hS: 2≤ size)
lemma BJ (u v: Fin N) (R: y7 S u v):
   ¬S.ND.Mm R.root v↔
     (S.tT ids hi hSize hS).leader u≠(S.tT ids hi hSize hS).leader v:= by
 have hU:=S.iR ids hi hSize hS R.root R.state R.present u R.K5
 rw [hU]
 constructor
 · intro hNo hEq
   have hOwner: S.ND.owner v=some R.root:=by
     have hComp: S.ND.BB (tE.Hv G M S.MG ids hi) v=R.root:=hEq.symm
     cases hv: S.ND.owner v with
     | some r =>
       simp only [G8.BB,hv,Option.getD_some] at hComp
       simpa only [hComp] using hv
     | none =>
       have hRootOwner: S.ND.owner R.root=some R.root:=
         (S.ND.KP R.root R.root).mpr ⟨R.state,R.present,R.state.tree.MU⟩
       have hSame:=S.ND.t7 S.MG ids hi v
       simp only [G8.BB,hv,Option.getD_none] at hComp
       rw [hComp] at hSame
       rw [hRootOwner,hv] at hSame
       cases hSame
   exact hNo ((S.ND.KP R.root v).mp hOwner)
 · intro hNe hContains
   exact hNe ((S.iR ids hi hSize hS R.root R.state R.present v
     (by obtain ⟨V,hV,hMem⟩:=hContains;have hh:=Option.some.inj (hV.symm.trans R.present);rwa [←hh])).symm)
lemma pT (mode: Bool) (u v: Fin N):
   ((S.tT ids hi hSize hS).leader u≠(S.tT ids hi hSize hS).leader v∧
     (if mode then Nonempty (y7 S u v)∨ Nonempty (y7 S v u)
       else S.Bd u v false∨ S.Bd v u false))↔
     s(u,v)∈(if mode then S.tZ else S.l9):= by
 cases mode with
 | true =>
   change (_∧(Nonempty (y7 S u v)∨ Nonempty (y7 S v u)))↔ s(u,v)∈S.tZ
   rw [S.kY]
   constructor
   · rintro ⟨hCross,hReq⟩
     rcases hReq with hReq|hReq
     · exact Or.inl ⟨hReq.some,(S.BJ ids hi hSize hS u v hReq.some).mpr hCross⟩
     · exact Or.inr ⟨hReq.some,(S.BJ ids hi hSize hS v u hReq.some).mpr hCross.symm⟩
   · rintro (⟨R,hNo⟩|⟨R,hNo⟩)
     · exact ⟨(S.BJ ids hi hSize hS u v R).mp hNo,Or.inl ⟨R⟩⟩
     · exact ⟨((S.BJ ids hi hSize hS v u R).mp hNo).symm,Or.inr ⟨R⟩⟩
 | false =>
   change (_∧(S.Bd u v false∨ S.Bd v u false))↔ s(u,v)∈S.l9
   rw [S.fG]
   unfold dJ
   rw [←S.kH,←S.kH]
   constructor
   · exact And.right
   · intro hReq
     refine ⟨?_,hReq⟩
     have hCross:∀a b,S.Bd a b false→
         (S.tT ids hi hSize hS).leader a≠(S.tT ids hi hSize hS).leader b:=by
       rintro a b ⟨R,hFlag⟩
       rw [S.iR ids hi hSize hS R.ME R.left R.HJ a R.M1,
         S.iR ids hi hSize hS R.L7 R.right R.GE b R.head_mem]
       exact R.distinct
     exact hReq.elim (hCross u v) (fun hh=>(hCross v u hh).symm)
end tI
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
def Hz (G: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (E: Finset (Sym2 (Fin N))) (v: Fin N): Finset ℕ:=
 ((G.neighborFinset v).filter (fun w=>s(v,w)∈E)).image ids
lemma Am (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (E: Finset (Sym2 (Fin N))) (u v: Fin N):
   ids v∈Hz G ids E u↔ G.Adj u v∧ s(u,v)∈E:= by
 simp only [Hz,mem_image,mem_filter,SimpleGraph.mem_neighborFinset]
 constructor
 · rintro ⟨w,⟨hEdge,hE⟩,hID⟩
   have hWV:=hi hID
   subst w
   exact ⟨hEdge,hE⟩
 · rintro ⟨hEdge,hE⟩
   exact ⟨v,⟨hEdge,hE⟩,rfl⟩
def FK (G: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (data: Fin N→ Ln) (E: Finset (Sym2 (Fin N))) (v: Fin N): Ln:=
 {data v with ignored:=(data v).ignored∪Hz G ids E v}
namespace Fi
variable {S: tI G M ell} {ids: Fin N→ ℕ} {hi: Function.Injective ids}
   {out: Fin N→ Option ℕ} {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (h: Fi S ids hi out hOut data)
include h in
lemma DI (E: Finset (Sym2 (Fin N)))
   (hM:∀u v,M.Adj u v→ s(u,v)∉E)
   (hMemory:∀r V,S.ND.state r=some V→∀u v,(u,v)∈V.tree.NS→ s(u,v)∉E):
   Fi (S.DH E hM hMemory) ids hi out hOut (FK G ids data E):= by
 refine ⟨h.neighbors,h.Jf,h.labels,h.Nm,?_,h.Jr,h.El,h.output⟩
 intro u v
 change (S.NV.Adj u v∧ s(u,v)∉E)↔ G.Adj u v∧(data u).Nm=false∧(data v).Nm=false∧
   ids v∉(data u).ignored∪Hz G ids E u∧ ids u∉(data v).ignored∪Hz G ids E v
 rw [h.NV]
 simp only [mem_union,not_or,Am ids hi]
 have hSwap: s(v,u)∈E↔ s(u,v)∈E:=by rw [Sym2.eq_swap]
 rw [hSwap]
 constructor
 · rintro ⟨⟨hG,hu,hv,hUV,hVU⟩,hE⟩
   exact ⟨hG,hu,hv,⟨hUV,fun hh=>hE hh.2⟩,⟨hVU,fun hh=>hE hh.2⟩⟩
 · rintro ⟨hG,hu,hv,⟨hUV,hUV'⟩,hVU,hVU'⟩
   exact ⟨⟨hG,hu,hv,hUV,hVU⟩,fun hh=>hUV' ⟨hG,hh⟩⟩
end Fi
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
structure Bl (S T: tI G M ell) (X: Finset (Fin N)): Prop where
 AB:∀r∈X,∀R,S.ND.state r=some R→ R.tree.vertices⊆X
 Aw:∀r∈X,∀R,T.ND.state r=some R→ R.tree.vertices⊆X
 DO:∀r,r∉X→ T.ND.state r=S.ND.state r
 D6:∀a,a.1∉X→ T.labels a=S.labels a
 HK:∀u,u∉X→∀v,v∉X→ S.NV.Adj u v→ T.NV.Adj u v
 Cy:∀u,u∉X→(u∈T.Nm↔ u∈S.Nm)
 Ev:∀u,u∉X→∀v,T.Et.Adj u v↔ S.Et.Adj u v
namespace Bl
variable {S T: tI G M ell} {X: Finset (Fin N)} (h: Bl S T X)
include h
lemma Go (v: Fin N) (hv: v∉X): T.ND.owner v=S.ND.owner v:= by
 cases hS: S.ND.owner v with
 | some r =>
   obtain ⟨R,hR,hVR⟩:=(S.ND.KP r v).mp hS
   have hr: r∉X:=fun hr=>hv (h.AB r hr R hR hVR)
   exact (T.ND.KP r v).mpr ⟨R,(h.DO r hr).trans hR,hVR⟩
 | none =>
   apply (T.ND.KN v).mpr
   rintro r ⟨R,hR,hVR⟩
   by_cases hr: r∈X
   · exact hv (h.Aw r hr R hR hVR)
   · have hOld: S.ND.state r=some R:=(h.DO r hr).symm.trans hR
     exact (S.ND.KN v).mp hS r ⟨R,hOld,hVR⟩
variable {P: ℕ} {H K: SimpleGraph (Fin P)} {U: tI H K ell}
   {E: wF H K G M}
lemma vJ (F: Db E U S)
   (hSeparate:∀u,u∉U.Nm→ E.toFun u∉X): Db E U T:= by
 refine ⟨?_,?_,?_,?_⟩
 · intro r R hR
   rw [h.DO (E.toFun r) (hSeparate r (U.vI r R hR))]
   exact F.present r R hR
 · intro u v hLive
   have hUV:=U.HK u v hLive
   exact h.HK _ (hSeparate u hUV.1) _ (hSeparate v hUV.2) (F.NV u v hLive)
 · intro a hA
   rw [h.D6 (E.pairMap a) (hSeparate a.1 hA)]
   exact F.labels a hA
 · intro u hU
   rw [h.Go _ (hSeparate u hU)]
   exact F.owner u hU
end Bl
end Be
end
noncomputable section
namespace Be.G8
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
lemma A6 (F H: G8 G M) {a: Fin N} (A: Lp G M a)
   (hA:∃B,F.state a=some B) (hH: H.state=Function.update F.state a (some A)) (r: Fin N):
   (∃R,H.state r=some R)↔∃R,F.state r=some R:= by
 rw [hH]
 by_cases hRA: r=a
 · subst r
   rw [Function.update_self]
   exact ⟨fun _=>hA,fun _=>⟨A,rfl⟩⟩
 · rw [Function.update_of_ne hRA]
lemma A7 (F H: G8 G M) {a b: Fin N} (A: Lp G M a) (B: Lp G M b)
   (hA:∃R,F.state a=some R) (hB:∃R,F.state b=some R)
   (hH: H.state=F.E2 A B) (r: Fin N):
   (∃R,H.state r=some R)↔∃R,F.state r=some R:= by
 rw [hH]
 by_cases hRB: r=b
 · subst r
   rw [F.E3]
   exact ⟨fun _=>hB,fun _=>⟨B,rfl⟩⟩
 · by_cases hRA: r=a
   · subst r
     rw [F.CZ hRB]
     exact ⟨fun _=>hA,fun _=>⟨A,rfl⟩⟩
   · rw [F.C0 A B r hRA hRB]
end Be.G8
namespace Be.Bb
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ} {S: tI G M ell}
   {x y: Fin N} {R: y7 S x y}
lemma JG (A: Bb R) (r: Fin N):
   (∃Q,A.Nj.ND.state r=some Q)↔∃Q,S.ND.state r=some Q:= by
 cases A with
 | single hOwner => exact G8.A6 S.ND _ _ ⟨R.state,R.present⟩ rfl r
 | inactive D B hB hAT hBT hStem hTarget hInactive =>
   exact G8.A7 S.ND _ _ _ ⟨R.state,R.present⟩ ⟨B,hB⟩ rfl r
 | active D B hB hAT hBT hStem hTarget hActive =>
   exact G8.A7 S.ND _ _ _ ⟨R.state,R.present⟩ ⟨B,hB⟩ rfl r
end Be.Bb
namespace Be.qF
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ} {S: tI G M ell}
   {x y: Fin N}
lemma JG (R: qF S x y) (r: Fin N):
   (∃Q,(S.sE R).ND.state r=some Q)↔
     (∃Q,S.ND.state r=some Q)∧ r≠R.ME∧ r≠R.L7:= by
 change (∃Q,(if r∈({R.ME,R.L7}: Finset (Fin N)) then none else S.ND.state r)=some Q)↔ _
 by_cases hR: r=R.ME∨ r=R.L7
 · simp only [mem_insert,mem_singleton,if_pos hR]
   simp only [Option.noConfusion,exists_false,ne_eq,not_and,not_or] at*
   tauto
 · simp only [mem_insert,mem_singleton,if_neg hR]
   exact ⟨fun h=>⟨h,not_or.mp hR⟩,And.left⟩
end Be.qF
end
noncomputable section
namespace Be.IO.NR
variable {D: IO} {ell: ℕ} {S: tI D.history.graph D.history.MG ell}
   {N: ℕ} {G M: SimpleGraph (Fin N)} {T: tI G M ell}
   {E: wF D.history.graph D.history.MG G M}
   (F: Db E S T) {mode: Bool} {u v: Fin D.history.keys.card}
lemma In (W: NR S mode u v): S.Nm⊆W.result.Nm:= by
 cases W with
 | augmentation R h => exact subset_union_left
 | extension hmode R hNo A => cases A<;> exact subset_refl _
lemma yB (W: NR S mode u v) (r: Fin N)
   (hR:∃R,(W.LT F).ND.state r=some R):∃R,T.ND.state r=some R:= by
 cases W with
 | augmentation R h => exact ((R.Nd F).JG r).mp hR|>.1
 | extension hmode R hNo A => exact ((A.Nd F).JG r).mp hR
lemma rQ (W: NR S mode u v) (a: Fin D.history.keys.card)
   (hOld:∃R,S.ND.state a=some R)
   (hPhysical:∃R,(W.LT F).ND.state (E.toFun a)=some R):
   ∃R,W.result.ND.state a=some R:= by
 cases W with
 | augmentation R h =>
   obtain ⟨hBefore,hLeft,hRight⟩:=((R.Nd F).JG (E.toFun a)).mp hPhysical
   exact (R.JG a).mpr ⟨hOld,fun hEq=>hLeft (congrArg E.toFun hEq),
     fun hEq=>hRight (congrArg E.toFun hEq)⟩
 | extension hmode R hNo A => exact (A.JG a).mpr hOld
end Be.IO.NR
end
noncomputable section
namespace Be
namespace v9
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)}
   (E: wF G M H K) {r: Fin N} (Q: v9 G M r)
lemma i8 (lab: Fin P ×Fin P→ ℕ) (a: Fin P ×Fin P)
   (hOutside: a.1∉Set.range E.toFun∨ a.2∉Set.range E.toFun):
   (Q.Nd E).Nl lab a=lab a:= by
 apply dif_neg
 rintro ⟨i,hi,hEq⟩
 have hTail: E.toFun (Q.vertex (2*i+1))=a.1:=congrArg Prod.fst hEq
 have hHead: E.toFun (Q.vertex (2*i+2))=a.2:=congrArg Prod.snd hEq
 rcases hOutside with h|h
 · exact h ⟨_,hTail⟩
 · exact h ⟨_,hHead⟩
end v9
namespace Bb
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ} {S: tI G M ell}
   {x y: Fin N} {R: y7 S x y} (A: Bb R)
lemma Gf (v: Fin N) (hv: v∈A.Nf.support): v∉S.Nm:= by
 obtain ⟨C,hC,hActive,hModified,hExtended,hHeld⟩:=A.EG
 have hAlive:=A.Nj.k7 R.root C hC v
   (C.tree.EA A.Nf (C.inside A.Nf hActive) hv)
 have hRemoved: A.Nj.Nm=S.Nm:=by cases A<;> rfl
 rwa [hRemoved] at hAlive
lemma gK (a: Fin N ×Fin N) (hTail: a.1∈S.Nm∨ a.2∈S.Nm):
   A.Nj.labels a=S.labels a:= by
 rw [A.LO]
 apply dif_neg
 rintro ⟨i,hi,hEq⟩
 rcases hTail with hTail|hHead
 · have hT: A.Nf.vertex (2*i+1)=a.1:=congrArg Prod.fst hEq
   exact A.Gf a.1 (hT ▸A.Nf.mem_support _ (by omega)) hTail
 · have hH: A.Nf.vertex (2*i+2)=a.2:=congrArg Prod.snd hEq
   exact A.Gf a.2 (hH ▸A.Nf.mem_support _ (by omega)) hHead
end Bb
end Be
end
noncomputable section
namespace Be.C3
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)}
   (E: wF G M H K) (Q: C3 G M)
lemma xD (u v: Fin N):
   (Q.Nd E).added.Adj (E.toFun u) (E.toFun v)↔ Q.added.Adj u v:= by
 rw [(Q.Nd E).Lr,Q.Lr]
 constructor
 · rintro ⟨i,hi,h|h⟩
   · exact ⟨i,hi,Or.inl ⟨E.injective h.1,E.injective h.2⟩⟩
   · exact ⟨i,hi,Or.inr ⟨E.injective h.1,E.injective h.2⟩⟩
 · rintro ⟨i,hi,h|h⟩
   · exact ⟨i,hi,Or.inl ⟨congrArg E.toFun h.1,congrArg E.toFun h.2⟩⟩
   · exact ⟨i,hi,Or.inr ⟨congrArg E.toFun h.1,congrArg E.toFun h.2⟩⟩
lemma Jz (u v: Fin N): Q.Nm.Adj u v↔
   ∃i,i< Q.length∧((u=Q.vertex (2*i+1)∧ v=Q.vertex (2*i+2))∨
     (u=Q.vertex (2*i+2)∧ v=Q.vertex (2*i+1))):= by
 constructor
 · rintro ⟨hG,h⟩
   obtain ⟨i,hi,hEq⟩:=mem_image.mp h
   exact ⟨i,mem_range.mp hi,Sym2.eq_iff.mp hEq.symm⟩
 · rintro ⟨i,hi,h⟩
   have hEq: s(u,v)=s(Q.vertex (2*i+1),Q.vertex (2*i+2)):=Sym2.eq_iff.mpr h
   refine ⟨(G.adj_congr_of_sym2 hEq).mpr ?_,mem_image.mpr ⟨i,mem_range.mpr hi,hEq.symm⟩⟩
   have hG:=Q.Mu (2*i+1) (by omega)
   simpa only [Nat.add_assoc] using hG
lemma rT (u v: Fin N):
   (Q.Nd E).Nm.Adj (E.toFun u) (E.toFun v)↔ Q.Nm.Adj u v:= by
 rw [(Q.Nd E).Jz,Q.Jz]
 constructor
 · rintro ⟨i,hi,h|h⟩
   · exact ⟨i,hi,Or.inl ⟨E.injective h.1,E.injective h.2⟩⟩
   · exact ⟨i,hi,Or.inr ⟨E.injective h.1,E.injective h.2⟩⟩
 · rintro ⟨i,hi,h|h⟩
   · exact ⟨i,hi,Or.inl ⟨congrArg E.toFun h.1,congrArg E.toFun h.2⟩⟩
   · exact ⟨i,hi,Or.inr ⟨congrArg E.toFun h.1,congrArg E.toFun h.2⟩⟩
lemma rR {u v: Fin P} (h:(Q.Nd E).added.Adj u v):
   u∈Set.range E.toFun∧ v∈Set.range E.toFun:= by
 obtain ⟨i,hi,h|h⟩:=(Q.Nd E).Lr u v|>.mp h
 · exact ⟨⟨Q.vertex (2*i),h.1.symm⟩,⟨Q.vertex (2*i+1),h.2.symm⟩⟩
 · exact ⟨⟨Q.vertex (2*i+1),h.1.symm⟩,⟨Q.vertex (2*i),h.2.symm⟩⟩
def wX: wF G (exchange M Q.Nm Q.added)
   H (exchange K (Q.Nd E).Nm (Q.Nd E).added) where
 toFun:=E.toFun
 injective:=E.injective
 LH:=E.LH
 HS:=by
   intro u v
   change ((K.Adj (E.toFun u) (E.toFun v)∧¬(Q.Nd E).Nm.Adj (E.toFun u) (E.toFun v))∨
     (Q.Nd E).added.Adj (E.toFun u) (E.toFun v))↔ _
   rw [E.HS,Q.rT E,Q.xD E]
   rfl
 B7:=by
   intro u w h
   rcases h with h|h
   · exact E.B7 u w h.1
   · exact (Q.rR E h).2
end Be.C3
end
noncomputable section
namespace Be.tI
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ} (S: tI G M ell)
lemma mS (u v: Fin N)
   (h:(Ld G S.found (fun P=>P.added)).Adj u v): u∈S.Nm∧ v∈S.Nm:= by
 obtain ⟨P,hP,hEdge⟩:=(E1 G S.found (fun P=>P.added)
   (fun P _=>zD.AN G P.J6) u v).mp h
 have hIn: s(u,v)∈P.added.edgeFinset:=P.added.mem_edgeFinset.mpr (P.added.mem_edgeSet.mpr hEdge)
 exact ⟨S.Hu (mem_biUnion.mpr ⟨P,hP,P.Fp _ hIn u (by simp)⟩),
   S.Hu (mem_biUnion.mpr ⟨P,hP,P.Fp _ hIn v (by simp)⟩)⟩
lemma iW (u v: Fin N)
   (h:(Ld G S.found (fun P=>P.Nm)).Adj u v): u∈S.Nm∧ v∈S.Nm:= by
 obtain ⟨P,hP,hEdge⟩:=(E1 G S.found (fun P=>P.Nm)
   (fun P _=>zD.AN G P.Il) u v).mp h
 have hIn: s(u,v)∈P.Nm.edgeFinset:=P.Nm.mem_edgeFinset.mpr (P.Nm.mem_edgeSet.mpr hEdge)
 exact ⟨S.Hu (mem_biUnion.mpr ⟨P,hP,P.Cz _ hIn u (by simp)⟩),
   S.Hu (mem_biUnion.mpr ⟨P,hP,P.Cz _ hIn v (by simp)⟩)⟩
lemma Cp (u v: Fin N) (hU: u∉S.Nm): S.Et.Adj u v↔ M.Adj u v:= by
 have hAdd:¬(Ld G S.found (fun P=>P.added)).Adj u v:=fun h=>hU (S.mS u v h).1
 have hRem:¬(Ld G S.found (fun P=>P.Nm)).Adj u v:=fun h=>hU (S.iW u v h).1
 change ((M.Adj u v∧¬(Ld G S.found (fun P=>P.Nm)).Adj u v)∨
   (Ld G S.found (fun P=>P.added)).Adj u v)↔ _
 simp only [hAdd,hRem,not_false_eq_true,and_true,or_false]
end Be.tI
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {I: Type}
lemma n3 (F: Finset I) (x: I) (H: I→ SimpleGraph (Fin N))
   (hH:∀i,H i≤ G): Ld G (insert x F) H=H x⊔Ld G F H:= by
 ext u v
 rw [E1 G (insert x F) H (fun i _=>hH i)]
 change (∃i,i∈insert x F∧(H i).Adj u v)↔(H x).Adj u v∨(Ld G F H).Adj u v
 rw [E1 G F H (fun i _=>hH i)]
 simp only [mem_insert]
 constructor
 · rintro ⟨i,hi,hEdge⟩
   rcases hi with rfl|hi
   · exact Or.inl hEdge
   · exact Or.inr ⟨i,hi,hEdge⟩
 · rintro (h|⟨i,hi,h⟩)
   · exact ⟨x,Or.inl rfl,h⟩
   · exact ⟨i,Or.inr hi,h⟩
end Be
end
noncomputable section
namespace Be
namespace C3
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
lemma Kd (P Q: C3 G M) (hLength: P.length=Q.length) (hVertex: P.vertex=Q.vertex): P=Q:= by
 cases P
 cases Q
 cases hLength
 cases hVertex
 rfl
end C3
namespace qF
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)} {ell: ℕ}
   {E: wF G M H K} {S: tI G M ell}
   {T: tI H K ell} (F: Db E S T)
   {x y: Fin N} (R: qF S x y)
def MD: C3 G M:=R.path.NM (show Mv G _≤ G from fun _ _ h=>h.1)
lemma Ah:(R.Nd F).MD=R.MD.Nd E:= by
 apply C3.Kd<;> rfl
lemma r9 (u v: Fin N) (hU: u∉S.Nm):
   (S.sE R).Et.Adj u v↔
     (exchange M R.MD.Nm R.MD.added).Adj u v:= by
 have hAdd:¬(Ld G S.found (fun P=>P.added)).Adj u v:=fun h=>hU (S.mS u v h).1
 have hRem:¬(Ld G S.found (fun P=>P.Nm)).Adj u v:=fun h=>hU (S.iW u v h).1
 change (exchange M (Ld G (insert R.MD S.found) (fun P=>P.Nm))
   (Ld G (insert R.MD S.found) (fun P=>P.added))).Adj u v↔ _
 rw [n3 S.found R.MD (fun P=>P.Nm)
     (fun P=>zD.AN G P.Il),
   n3 S.found R.MD (fun P=>P.added)
     (fun P=>zD.AN G P.J6)]
 change ((M.Adj u v∧¬(R.MD.Nm.Adj u v∨(Ld G S.found (fun P=>P.Nm)).Adj u v))∨
   R.MD.added.Adj u v∨(Ld G S.found (fun P=>P.added)).Adj u v)↔ _
 simp only [hAdd,hRem,or_false]
 rfl
lemma k6 (u v: Fin N) (hU: u∉R.MD.support):
   (S.sE R).Et.Adj u v↔ S.Et.Adj u v:= by
 have hAdd:¬R.MD.added.Adj u v:=by
   intro hEdge
   exact hU (R.MD.Fp s(u,v)
     (R.MD.added.mem_edgeFinset.mpr (R.MD.added.mem_edgeSet.mpr hEdge)) u (by simp))
 have hRem:¬R.MD.Nm.Adj u v:=by
   intro hEdge
   exact hU (R.MD.Cz s(u,v)
     (R.MD.Nm.mem_edgeFinset.mpr (R.MD.Nm.mem_edgeSet.mpr hEdge)) u (by simp))
 change (exchange M (Ld G (insert R.MD S.found) (fun P=>P.Nm))
   (Ld G (insert R.MD S.found) (fun P=>P.added))).Adj u v↔ _
 rw [n3 S.found R.MD (fun P=>P.Nm)
     (fun P=>zD.AN G P.Il),
   n3 S.found R.MD (fun P=>P.added)
     (fun P=>zD.AN G P.J6)]
 change ((M.Adj u v∧¬(R.MD.Nm.Adj u v∨(Ld G S.found (fun P=>P.Nm)).Adj u v))∨
   R.MD.added.Adj u v∨(Ld G S.found (fun P=>P.added)).Adj u v)↔ _
 simp only [hAdd,hRem,false_or]
 rfl
lemma sA (u v: Fin N) (hU: u∉S.Nm) (hPhys: E.toFun u∉T.Nm):
   (T.sE (R.Nd F)).Et.Adj (E.toFun u) (E.toFun v)↔
     (S.sE R).Et.Adj u v:= by
 rw [(R.Nd F).r9 (E.toFun u) (E.toFun v) hPhys,
   R.r9 u v hU,R.Ah F]
 exact (R.MD.wX E).HS u v
lemma k5 (u: Fin N) (hPhys: E.toFun u∉T.Nm) (w: Fin P)
   (hEdge:(T.sE (R.Nd F)).Et.Adj (E.toFun u) w):
   ∃v,E.toFun v=w:= by
 rw [(R.Nd F).r9 (E.toFun u) w hPhys,R.Ah F] at hEdge
 exact (R.MD.wX E).B7 u w hEdge
end qF
end Be
end
noncomputable section
namespace Be.IO.NR
variable {D: IO} {ell: ℕ} {S: tI D.history.graph D.history.MG ell}
   {N: ℕ} {G M: SimpleGraph (Fin N)} {T: tI G M ell}
   {E: wF D.history.graph D.history.MG G M}
   (F: Db E S T) {mode: Bool} {u v: Fin D.history.keys.card}
   (X: Finset (Fin N))
   (hImage:∀a,a∉S.Nm→ E.toFun a∈X)
   (hCover:∀r∈X,∀R,T.ND.state r=some R→
     ∃a A,S.ND.state a=some A∧ E.toFun a=r)
include F hImage
lemma Cm {r: Fin D.history.keys.card} (R: Lp D.history.graph D.history.MG r)
   (hR: S.ND.state r=some R):(R.Nd E).tree.vertices⊆X:= by
 rw [R.Aj E]
 intro b hb
 obtain ⟨a,ha,hAB⟩:=mem_image.mp hb
 exact hAB ▸hImage a (S.k7 r R hR a ha)
include hCover in
lemma gW (r: Fin N) (hr: r∈X) (R: Lp G M r)
   (hR: T.ND.state r=some R): R.tree.vertices⊆X:= by
 obtain ⟨a,A,hA,hAR⟩:=hCover r hr R hR
 subst r
 have hEq: A.Nd E=R:=Option.some.inj ((F.present a A hA).symm.trans hR)
 rw [←hEq]
 exact Cm F X hImage A hA
include hCover in
lemma gV (W: NR S mode u v) (r: Fin N) (hr: r∈X) (R: Lp G M r)
   (hR:(W.LT F).ND.state r=some R): R.tree.vertices⊆X:= by
 obtain ⟨A,hA⟩:=W.yB F r ⟨R,hR⟩
 obtain ⟨a,B,hB,hAR⟩:=hCover r hr A hA
 subst r
 obtain ⟨C,hC⟩:=W.rQ F a ⟨B,hB⟩ ⟨R,hR⟩
 have hEq: C.Nd E=R:=Option.some.inj ((W.Kz F a C hC).symm.trans hR)
 rw [←hEq,C.Aj E]
 intro b hb
 obtain ⟨c,hc,hCB⟩:=mem_image.mp hb
 exact hCB ▸hImage c (fun hOld=>W.result.k7 a C hC c hc (W.In hOld))
lemma DO (W: NR S mode u v) (r: Fin N) (hr: r∉X):
   (W.LT F).ND.state r=T.ND.state r:= by
 have hNe:∀a A,S.ND.state a=some A→ r≠E.toFun a:=by
   intro a A hA hEq
   subst r
   exact hr (hImage a (S.vI a A hA))
 cases W with
 | augmentation R h =>
   change (if r∈({E.toFun R.ME,E.toFun R.L7}: Finset (Fin N)) then none else T.ND.state r)=_
   simp only [mem_insert,mem_singleton,hNe R.ME R.left R.HJ,
     hNe R.L7 R.right R.GE,false_or,if_false]
 | extension hmode R hNo A =>
   cases A with
   | single hOwner =>
     change Function.update T.ND.state (E.toFun R.root) _ r=T.ND.state r
     dsimp only [y7.Nd]
     rw [Function.update_of_ne (hNe R.root R.state R.present)]
   | inactive L B hB hAT hBT hStem hTarget hInactive =>
     change T.ND.E2 _ _ r=T.ND.state r
     exact T.ND.C0 _ _ r (hNe R.root R.state R.present) (hNe _ B hB)
   | active L B hB hAT hBT hStem hTarget hActive =>
     change T.ND.E2 _ _ r=T.ND.state r
     exact T.ND.C0 _ _ r (hNe R.root R.state R.present) (hNe _ B hB)
lemma D6 (W: NR S mode u v) (a: Fin N ×Fin N) (hA: a.1∉X):
   (W.LT F).labels a=T.labels a:= by
 cases W with
 | augmentation R h => rfl
 | extension hmode R hNo A =>
   rw [LT,(A.Nd F).LO,A.Ju F]
   apply dif_neg
   rintro ⟨i,hi,hEq⟩
   have hTail: E.toFun (A.Nf.vertex (2*i+1))=a.1:=congrArg Prod.fst hEq
   have hLocal: A.Nf.vertex (2*i+1)∉S.Nm:=A.Gf _
     (A.Nf.mem_support _ (by change i< A.Nf.length at hi;omega))
   exact hA (hTail ▸hImage _ hLocal)
lemma HK (W: NR S mode u v) (a: Fin N) (hA: a∉X) (b: Fin N) (hB: b∉X)
   (hLive: T.NV.Adj a b):(W.LT F).NV.Adj a b:= by
 cases W with
 | augmentation R h =>
   have hDel:((R.left.Nd E).tree.vertices∪(R.right.Nd E).tree.vertices)⊆X:=
     union_subset (Cm F X hImage R.left R.HJ) (Cm F X hImage R.right R.GE)
   exact ⟨hLive,fun ha=>hA (hDel ha),fun hb=>hB (hDel hb)⟩
 | extension hmode R hNo A => cases A<;> exact hLive
lemma Cy (W: NR S mode u v) (a: Fin N) (hA: a∉X):
   a∈(W.LT F).Nm↔ a∈T.Nm:= by
 cases W with
 | augmentation R h =>
   have hDel:((R.left.Nd E).tree.vertices∪(R.right.Nd E).tree.vertices)⊆X:=
     union_subset (Cm F X hImage R.left R.HJ) (Cm F X hImage R.right R.GE)
   change a∈T.Nm∪((R.left.Nd E).tree.vertices∪(R.right.Nd E).tree.vertices)↔ _
   simp only [mem_union]
   exact or_iff_left (fun ha=>hA (hDel (mem_union.mpr ha)))
 | extension hmode R hNo A => cases A<;> rfl
lemma Ev (W: NR S mode u v) (a: Fin N) (hA: a∉X) (b: Fin N):
   (W.LT F).Et.Adj a b↔ T.Et.Adj a b:= by
 cases W with
 | augmentation R h =>
   have hDel:((R.left.Nd E).tree.vertices∪(R.right.Nd E).tree.vertices)⊆X:=
     union_subset (Cm F X hImage R.left R.HJ) (Cm F X hImage R.right R.GE)
   let L:=R.Nd F
   have hSupport: L.MD.support⊆L.left.tree.vertices∪L.right.tree.vertices:=
     L.left.tree.cR L.right.tree _ _ L.M1 L.head_mem L.path
   exact L.k6 a b (fun hMem=>hA (hDel (hSupport hMem)))
 | extension hmode R hNo A => cases A<;> rfl
include hCover in
lemma supported (W: NR S mode u v): Bl T (W.LT F) X:=
 ⟨gW F X hImage hCover,gV F X hImage hCover W,
   W.DO F X hImage,W.D6 F X hImage,W.HK F X hImage,
   W.Cy F X hImage,W.Ev F X hImage⟩
end Be.IO.NR
end
noncomputable section
namespace Be
namespace Db
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)} {ell: ℕ}
   {E: wF G M H K} {S: tI G M ell} {T: tI H K ell}
   (F: Db E S T)
include F in
lemma alive (u: Fin N) (hU: u∉S.Nm): E.toFun u∉T.Nm:= by
 by_cases hMate:∃v,M.Adj u v
 · obtain ⟨v,hV⟩:=hMate
   exact (T.HK _ _ (F.NV u v (S.HQ u v hV hU))).1
 · have hFree:∀v,¬M.Adj u v:=by simpa only [not_exists] using hMate
   obtain ⟨R,hR⟩:=S.Iu u hFree hU
   exact T.vI _ _ (F.present u R hR)
end Db
structure Bh {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)} {ell: ℕ}
   (E: wF G M H K) (U: tI G M ell)
   (X: Finset (Fin P)) (S: tI H K ell): Prop where
 frame: Db E U S
 image:∀a,a∉U.Nm→ E.toFun a∈X
 IV:∀v∈X,v∉S.Nm→∃a,a∉U.Nm∧ E.toFun a=v
 cover:∀r∈X,∀R,S.ND.state r=some R→∃a A,U.ND.state a=some A∧ E.toFun a=r
namespace Bh
variable {N P: ℕ} {G M: SimpleGraph (Fin N)} {H K: SimpleGraph (Fin P)} {ell: ℕ}
   {E: wF G M H K} {U: tI G M ell} {X Y: Finset (Fin P)}
   {S T: tI H K ell} (R: Bh E U X S)
include R in
lemma L4 (h: Bl S T Y) (hDisjoint: Disjoint X Y): Bh E U X T:= by
 refine ⟨h.vJ R.frame (fun a ha hY=>disjoint_left.mp hDisjoint (R.image a ha) hY),R.image,?_,?_⟩
 · intro v hv hAlive
   have hvY: v∉Y:=fun hY=>disjoint_left.mp hDisjoint hv hY
   apply R.IV v hv
   exact fun hOld=>hAlive ((h.Cy v hvY).mpr hOld)
 · intro r hr A hA
   have hrY: r∉Y:=fun hrY=>disjoint_left.mp hDisjoint hr hrY
   rw [h.DO r hrY] at hA
   exact R.cover r hr A hA
end Bh
namespace IO.NR
variable {D: IO} {ell: ℕ} {U: tI D.history.graph D.history.MG ell}
   {N: ℕ} {G M: SimpleGraph (Fin N)} {S: tI G M ell}
   {E: wF D.history.graph D.history.MG G M} {X: Finset (Fin N)}
   (R: Bh E U X S) {mode: Bool} {u v: Fin D.history.keys.card}
lemma AX (W: NR U mode u v): Bl S (W.LT R.frame) X:=
 W.supported R.frame X R.image R.cover
end IO.NR
end Be
end
noncomputable section
namespace Be.IO.NR
variable {D: IO} {ell: ℕ} {S: tI D.history.graph D.history.MG ell}
   {N: ℕ} {G M: SimpleGraph (Fin N)} {T: tI G M ell}
   {E: wF D.history.graph D.history.MG G M}
   (F: Db E S T) {mode: Bool} {u v: Fin D.history.keys.card}
lemma Kx (W: NR S mode u v) (a: Fin D.history.keys.card ×Fin D.history.keys.card)
   (hA: a.1∉S.Nm):(W.LT F).labels (E.pairMap a)=W.result.labels a:= by
 cases W with
 | augmentation R h => exact F.labels a hA
 | extension hmode R hNo A => exact A.vC F a hA
lemma JA (W: NR S mode u v) (a: Fin D.history.keys.card)
   (hA: a∉S.Nm) (hPhys: E.toFun a∉T.Nm):
   a∈W.result.Nm↔ E.toFun a∈(W.LT F).Nm:= by
 cases W with
 | augmentation R h => exact R.JA F a hA hPhys
 | extension hmode R hNo A =>
   cases A<;> simpa only [LT,Bb.Nd,Bb.Nj,
     tI.Kg,tI.AE,tI.Ew,
     tI.JC,tI.JB,IO.NR.result,hA,hPhys]
lemma sA (W: NR S mode u v) (a b: Fin D.history.keys.card)
   (hA: a∉S.Nm) (hPhys: E.toFun a∉T.Nm):
   (W.LT F).Et.Adj (E.toFun a) (E.toFun b)↔ W.result.Et.Adj a b:= by
 cases W with
 | augmentation R h => exact R.sA F a b hA hPhys
 | extension hmode R hNo A =>
   have hLocal: A.Nj.Et=S.Et:=by cases A<;> rfl
   have hGlobal:(A.Nd F).Nj.Et=T.Et:=by cases A<;> rfl
   change (A.Nd F).Nj.Et.Adj _ _↔ A.Nj.Et.Adj _ _
   rw [hLocal,hGlobal,S.Cp a b hA,T.Cp _ _ hPhys]
   exact E.HS a b
lemma k5 (W: NR S mode u v) (a: Fin D.history.keys.card)
   (hPhys: E.toFun a∉T.Nm) (w: Fin N)
   (hEdge:(W.LT F).Et.Adj (E.toFun a) w):∃b,E.toFun b=w:= by
 cases W with
 | augmentation R h => exact R.k5 F a hPhys w hEdge
 | extension hmode R hNo A =>
   have hGlobal:(A.Nd F).Nj.Et=T.Et:=by cases A<;> rfl
   change (A.Nd F).Nj.Et.Adj _ _ at hEdge
   rw [hGlobal,T.Cp _ _ hPhys] at hEdge
   exact E.B7 a w hEdge
end Be.IO.NR
end
noncomputable section
namespace Be.IO.NR
variable {D: IO} {ell: ℕ} {U: tI D.history.graph D.history.MG ell}
   {N: ℕ} {G M: SimpleGraph (Fin N)} {S: tI G M ell}
   {E: wF D.history.graph D.history.MG G M} {X: Finset (Fin N)}
   (R: Bh E U X S) {mode: Bool} {u v: Fin D.history.keys.card}
lemma nM (W: NR U mode u v): S.Nm⊆(W.LT R.frame).Nm:= by
 cases W with
 | augmentation A h => exact subset_union_left
 | extension hmode A hNo B => cases B<;> exact subset_refl _
lemma LS (W: NR U mode u v): W.result.NV≤ U.NV:= by
 cases W with
 | augmentation A h => exact fun _ _ h=>h.1
 | extension hmode A hNo B => cases B<;> exact le_refl _
lemma sH (W: NR U mode u v) (a b: Fin N) (hEdge: S.NV.Adj a b)
   (ha: a∉(W.LT R.frame).Nm) (hb: b∉(W.LT R.frame).Nm):
   (W.LT R.frame).NV.Adj a b:= by
 cases W with
 | augmentation A h =>
   exact ⟨hEdge,fun hD=>ha (mem_union_right _ hD),fun hD=>hb (mem_union_right _ hD)⟩
 | extension hmode A hNo B => cases B<;> exact hEdge
lemma IU (W: NR U mode u v):∀r∈X,∀A,
   (W.LT R.frame).ND.state r=some A→
     ∃a B,W.result.ND.state a=some B∧ E.toFun a=r:= by
 intro r hr A hA
 obtain ⟨B,hB⟩:=W.yB R.frame r ⟨A,hA⟩
 obtain ⟨a,C,hC,hAR⟩:=R.cover r hr B hB
 subst r
 obtain ⟨Q,hQ⟩:=W.rQ R.frame a ⟨C,hC⟩ ⟨A,hA⟩
 exact ⟨a,Q,hQ,rfl⟩
lemma Hb (W: NR U mode u v): Bh E W.result X (W.LT R.frame):= by
 let V:=W.LT R.frame
 let L:=W.result
 have hOldAlive:∀a,a∉L.Nm→ a∉U.Nm:=by
   intro a ha hOld
   exact ha (W.In hOld)
 have hRemoved:∀a,a∉U.Nm→(a∈L.Nm↔ E.toFun a∈V.Nm):=by
   intro a ha
   exact W.JA R.frame a ha (R.frame.alive a ha)
 have hNewAlive:∀a,a∉L.Nm→ E.toFun a∉V.Nm:=by
   intro a ha hPhys
   exact ha ((hRemoved a (hOldAlive a ha)).mpr hPhys)
 have hCover:=W.IU R
 have hFrame: Db E L V:=by
   refine ⟨W.Kz R.frame,?_,?_,?_⟩
   · intro a b hEdge
     have hAB:=L.HK a b hEdge
     exact W.sH R _ _ (R.frame.NV a b (W.LS hEdge))
       (hNewAlive a hAB.1) (hNewAlive b hAB.2)
   · intro a ha
     exact W.Kx R.frame a (hOldAlive a.1 ha)
   · intro a ha
     cases hOwner: L.ND.owner a with
     | some b =>
       obtain ⟨B,hB,haB⟩:=(L.ND.KP b a).mp hOwner
       have hPhys: E.toFun a∈(B.Nd E).tree.vertices:=by
         rw [B.Aj E];exact mem_image.mpr ⟨a,haB,rfl⟩
       exact (V.ND.KP _ _).mpr ⟨B.Nd E,W.Kz R.frame b B hB,hPhys⟩
     | none =>
       apply (V.ND.KN _).mpr
       rintro r ⟨A,hA,haA⟩
       have hr: r∈X:=by
         by_contra hr
         have hEq:=W.DO R.frame X R.image r hr
         have hOldState: S.ND.state r=some A:=hEq.symm.trans hA
         have hOldOwner: S.ND.owner (E.toFun a)=some r:=(S.ND.KP _ _).mpr ⟨A,hOldState,haA⟩
         rw [R.frame.owner a (hOldAlive a ha)] at hOldOwner
         obtain ⟨b,hB,hBR⟩:=Option.map_eq_some_iff.mp hOldOwner
         obtain ⟨B,hState,hAB⟩:=(U.ND.KP b a).mp hB
         exact hr (hBR ▸R.image b (U.vI b B hState))
       obtain ⟨b,B,hB,hBR⟩:=hCover r hr A hA
       subst r
       have hEq: B.Nd E=A:=Option.some.inj ((W.Kz R.frame b B hB).symm.trans hA)
       rw [←hEq,B.Aj E] at haA
       obtain ⟨c,hc,hCA⟩:=mem_image.mp haA
       have hLocal: L.ND.owner a=some b:=(L.ND.KP _ _).mpr ⟨B,hB,E.injective hCA ▸hc⟩
       rw [hOwner] at hLocal
       cases hLocal
 refine ⟨hFrame,fun a ha=>R.image a (hOldAlive a ha),?_,hCover⟩
 intro a ha hAlive
 have hBefore: a∉S.Nm:=fun hOld=>hAlive (W.nM R hOld)
 obtain ⟨b,hB,hBA⟩:=R.IV a ha hBefore
 refine ⟨b,?_,hBA⟩
 intro hNew
 exact hAlive (hBA ▸(hRemoved b hB).mp hNew)
end Be.IO.NR
end
noncomputable section
namespace Be
variable {N P: ℕ}
lemma r3 (G J: SimpleGraph (Fin N)) (H L: SimpleGraph (Fin P))
   (f: Fin N→ Fin P) (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (physicalIds: Fin P→ ℕ) (hIDs:∀v,physicalIds (f v)=ids v)
   (hJ: Matching G J) (physicalOut: Fin P→ Option ℕ)
   (hOut: ReportsMatching H physicalIds physicalOut L) (u: Fin N)
   (hEdges:∀v,L.Adj (f u) (f v)↔ J.Adj u v)
   (hClosed:∀w,L.Adj (f u) w→∃v,f v=w):
   (tB.NW ids hi J u).map ids=physicalOut (f u):= by
 cases hMate: tB.NW ids hi J u with
 | none =>
   have hFree:=(tB.LV ids hi J u).mp hMate
   apply Eq.symm
   apply (hOut.2 (f u)).1.mpr
   intro w hEdge
   obtain ⟨v,rfl⟩:=hClosed w hEdge
   exact hFree v ((hEdges v).mp hEdge)
 | some v =>
   have hEdge:=(tB.LW ids hi J
     (qJ.gP G J hJ) u v).mp hMate
   have hReported: physicalOut (f u)=some (ids v):=(hOut.2 (f u)).2 (ids v)|>.mpr
     ⟨f v,(hEdges v).mpr hEdge,hIDs v⟩
   exact hReported.symm
end Be
end
noncomputable section
namespace Be.IO
structure IR {D: IO} {ell: ℕ}
   {U: tI D.history.graph D.history.MG ell}
   {N: ℕ} {G M: SimpleGraph (Fin N)}
   (E: wF D.history.graph D.history.MG G M)
   {mode: Bool} {u v: Fin D.history.keys.card} (W: NR U mode u v)
   (X: Finset (Fin N)) (S: tI G M ell): Prop where
 region: Bh E W.result X S
 L1:∀a,a∉U.Nm→ E.toFun a∈X
 labels:∀a,a.1∉U.Nm→ S.labels (E.pairMap a)=W.result.labels a
 Nm:∀a,a∉U.Nm→(a∈W.result.Nm↔ E.toFun a∈S.Nm)
 output:∀a,a∉U.Nm→∀b,
   S.Et.Adj (E.toFun a) (E.toFun b)↔ W.result.Et.Adj a b
 closed:∀a,a∉U.Nm→∀w,
   S.Et.Adj (E.toFun a) w→∃b,E.toFun b=w
namespace NR
variable {D: IO} {ell: ℕ} {U: tI D.history.graph D.history.MG ell}
   {N: ℕ} {G M: SimpleGraph (Fin N)} {S: tI G M ell}
   {E: wF D.history.graph D.history.MG G M} {X: Finset (Fin N)}
   (R: Bh E U X S) {mode: Bool} {u v: Fin D.history.keys.card}
lemma Nh (W: NR U mode u v): IR E W X (W.LT R.frame):=
 ⟨W.Hb R,R.image,W.Kx R.frame,
   fun a ha=>W.JA R.frame a ha (R.frame.alive a ha),
   fun a ha b=>W.sA R.frame a b ha (R.frame.alive a ha),
   fun a ha w=>W.k5 R.frame a (R.frame.alive a ha) w⟩
end NR
namespace IR
variable {D: IO} {ell: ℕ} {U: tI D.history.graph D.history.MG ell}
   {N: ℕ} {G M: SimpleGraph (Fin N)}
   {E: wF D.history.graph D.history.MG G M}
   {mode: Bool} {u v: Fin D.history.keys.card} {W: NR U mode u v}
   {X Y: Finset (Fin N)} {S T: tI G M ell} (R: IR E W X S)
include R in
lemma L4 (h: Bl S T Y) (hDisjoint: Disjoint X Y): IR E W X T:= by
 have hOutside:∀a,a∉U.Nm→ E.toFun a∉Y:=by
   intro a ha hY
   exact disjoint_left.mp hDisjoint (R.L1 a ha) hY
 refine ⟨R.region.L4 h hDisjoint,R.L1,?_,?_,?_,?_⟩
 · intro a ha
   rw [h.D6 (E.pairMap a) (hOutside a.1 ha)]
   exact R.labels a ha
 · intro a ha
   exact (R.Nm a ha).trans (h.Cy (E.toFun a) (hOutside a ha)).symm
 · intro a ha b
   exact (h.Ev (E.toFun a) (hOutside a ha) (E.toFun b)).trans (R.output a ha b)
 · intro a ha w hEdge
   exact R.closed a ha w ((h.Ev (E.toFun a) (hOutside a ha) w).mp hEdge)
include R in
lemma Jv (ids: Fin N→ ℕ) (hIDs:∀a,ids (E.toFun a)=D.history.identity a)
   (out: Fin N→ Option ℕ) (hOut: ReportsMatching G ids out S.Et)
   (a: Fin D.history.keys.card) (ha: a∉U.Nm): D.KM W.result a=out (E.toFun a):= by
 exact r3 D.history.graph W.result.Et G S.Et E.toFun
   D.history.identity D.history.identity_injective ids hIDs W.result.Eu.1 out hOut a
   (R.output a ha) (R.closed a ha)
end IR
end Be.IO
end
noncomputable section
namespace Be.Bl
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)}
   {S T V: tI G M ell} {X Y: Finset (Fin N)}
lemma identity (S: tI G M ell): Bl S S ∅:= by
 refine ⟨?_,?_,fun _ _=>rfl,fun _ _=>rfl,fun _ _ _ _ h=>h,fun _ _=>Iff.rfl,fun _ _ _=>Iff.rfl⟩
 · intro r hr;simp at hr
 · intro r hr;simp at hr
lemma zZ (h: Bl S T X) (k: Bl T V Y)
   (hDisjoint: Disjoint X Y): Bl S V (X∪Y):= by
 have hXY:∀r,r∈X→ r∉Y:=fun r hr hY=>disjoint_left.mp hDisjoint hr hY
 have hYX:∀r,r∈Y→ r∉X:=fun r hr hX=>disjoint_left.mp hDisjoint hX hr
 refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
 · intro r hr A hA v hv
   rcases mem_union.mp hr with hr|hr
   · exact mem_union_left _ (h.AB r hr A hA hv)
   · have hT: T.ND.state r=some A:=(h.DO r (hYX r hr)).trans hA
     exact mem_union_right _ (k.AB r hr A hT hv)
 · intro r hr A hA v hv
   rcases mem_union.mp hr with hr|hr
   · have hT: T.ND.state r=some A:=(k.DO r (hXY r hr)).symm.trans hA
     exact mem_union_left _ (h.Aw r hr A hT hv)
   · exact mem_union_right _ (k.Aw r hr A hA hv)
 · intro r hr
   have hR: r∉X∧ r∉Y:=by simpa only [mem_union,not_or] using hr
   exact (k.DO r hR.2).trans (h.DO r hR.1)
 · intro a ha
   have hA: a.1∉X∧ a.1∉Y:=by simpa only [mem_union,not_or] using ha
   exact (k.D6 a hA.2).trans (h.D6 a hA.1)
 · intro u hu v hv hEdge
   have hU: u∉X∧ u∉Y:=by simpa only [mem_union,not_or] using hu
   have hV: v∉X∧ v∉Y:=by simpa only [mem_union,not_or] using hv
   exact k.HK u hU.2 v hV.2 (h.HK u hU.1 v hV.1 hEdge)
 · intro u hu
   have hU: u∉X∧ u∉Y:=by simpa only [mem_union,not_or] using hu
   exact (k.Cy u hU.2).trans (h.Cy u hU.1)
 · intro u hu v
   have hU: u∉X∧ u∉Y:=by simpa only [mem_union,not_or] using hu
   exact (k.Ev u hU.2 v).trans (h.Ev u hU.1 v)
end Be.Bl
end
noncomputable section
namespace Be
structure JZ {N: ℕ} (G M: SimpleGraph (Fin N)) (ell: ℕ) (mode: Bool) where
 NI: IO
 view: tI NI.history.graph NI.history.MG ell
 embed: wF NI.history.graph NI.history.MG G M
 support: Finset (Fin N)
 tail: Fin NI.history.keys.card
 head: Fin NI.history.keys.card
 NY: IO.NR view mode tail head
namespace JZ
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)} {mode: Bool}
def Lj (A: JZ G M ell mode) (S: tI G M ell): Prop:=
 Bh A.embed A.view A.support S
def M6 (A: JZ G M ell mode) (S: tI G M ell): Prop:=
 IO.IR A.embed A.NY A.support S
def next (A: JZ G M ell mode) (S: tI G M ell) (h: A.Lj S):
   tI G M ell:=A.NY.LT h.frame
def LD (A: JZ G M ell mode): Fin N ×Fin N:=(A.embed.toFun A.tail,A.embed.toFun A.head)
def MZ: List (JZ G M ell mode)→ Finset (Fin N)
 | []=>∅
 | A::as=>A.support∪MZ as
lemma wU (as: List (JZ G M ell mode)) (X: Finset (Fin N))
   (h:∀A∈as,Disjoint X A.support): Disjoint X (MZ as):= by
 induction as with
 | nil => simp [MZ]
 | cons A as ih =>
   exact disjoint_union_right.mpr ⟨h A (List.mem_cons_self),ih (fun B hB=>h B (List.mem_cons_of_mem A hB))⟩
lemma Cj (A: JZ G M ell mode) (S: tI G M ell) (h: A.Lj S):
   Dd mode A.LD.1 A.LD.2 S (A.next S h):=A.NY.Ef h.frame
lemma Eo (A: JZ G M ell mode) (S: tI G M ell) (h: A.Lj S):
   Bl S (A.next S h) A.support:=A.NY.AX h
lemma H7 (A: JZ G M ell mode) (S: tI G M ell) (h: A.Lj S):
   A.M6 (A.next S h):=A.NY.Nh h
end JZ
end Be
end
noncomputable section
namespace Be.JZ
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)} {mode: Bool}
lemma kF
   (ExtraAvailable ExtraOutcome: JZ G M ell mode→ tI G M ell→ Prop)
   (step:∀A S (hA: A.Lj S),ExtraAvailable A S→ ExtraOutcome A (A.next S hA))
   (preserveAvailable:∀A S T Y,A.Lj S→ ExtraAvailable A S→
     Bl S T Y→ Disjoint A.support Y→ ExtraAvailable A T)
   (preserveOutcome:∀A S T Y,A.M6 S→ ExtraOutcome A S→
     Bl S T Y→ Disjoint A.support Y→ ExtraOutcome A T)
   (as: List (JZ G M ell mode))
   (hPairwise: as.Pairwise (fun A B=>Disjoint A.support B.support))
   (S: tI G M ell) (hAvailable:∀A∈as,A.Lj S)
   (hExtra:∀A∈as,ExtraAvailable A S):
   ∃T,Dc mode (as.map LD) S T∧ Bl S T (MZ as)∧
     ∀A∈as,A.M6 T∧ ExtraOutcome A T:= by
 induction as generalizing S with
 | nil => exact ⟨S,Dc.nil S,Bl.identity S,by intro A hA;simp at hA⟩
 | cons A as ih =>
   obtain ⟨hDisjoint,hPairs⟩:=List.pairwise_cons.mp hPairwise
   have hA: A.Lj S:=hAvailable A List.mem_cons_self
   let V:=A.next S hA
   have hStep: Dd mode A.LD.1 A.LD.2 S V:=A.Cj S hA
   have hSupport: Bl S V A.support:=A.Eo S hA
   have hTailAvailable:∀B∈as,B.Lj V:=by
     intro B hB
     exact (hAvailable B (List.mem_cons_of_mem A hB)).L4 hSupport (hDisjoint B hB).symm
   have hTailExtra:∀B∈as,ExtraAvailable B V:=by
     intro B hB
     exact preserveAvailable B S V A.support (hAvailable B (List.mem_cons_of_mem A hB))
       (hExtra B (List.mem_cons_of_mem A hB)) hSupport (hDisjoint B hB).symm
   obtain ⟨T,hPass,hTailSupport,hOutcomes⟩:=ih hPairs V hTailAvailable hTailExtra
   have hUnion: Disjoint A.support (MZ as):=wU as A.support hDisjoint
   refine ⟨T,Dc.cons hStep hPass,hSupport.zZ hTailSupport hUnion,?_⟩
   intro B hB
   rcases List.mem_cons.mp hB with hB|hB
   · subst B
     exact ⟨(A.H7 S hA).L4 hTailSupport hUnion,
       preserveOutcome A V T (MZ as) (A.H7 S hA)
         (step A S hA (hExtra A List.mem_cons_self)) hTailSupport hUnion⟩
   · exact hOutcomes B hB
end Be.JZ
end
noncomputable section
namespace Be.IO.NR
variable {D: IO} {ell: ℕ} {U: tI D.history.graph D.history.MG ell}
   {N: ℕ} {G M: SimpleGraph (Fin N)} {S: tI G M ell}
   {E: wF D.history.graph D.history.MG G M}
   (F: Db E U S) {mode: Bool} {u v: Fin D.history.keys.card}
lemma o7 (W: NR U mode u v) (a: Fin D.history.keys.card) (w: Fin N)
   (hW: w∉Set.range E.toFun):(W.LT F).labels (E.toFun a,w)=S.labels (E.toFun a,w):= by
 cases W with
 | augmentation R h => rfl
 | extension hMode R hNo A =>
   rw [LT,(A.Nd F).LO,A.Ju F]
   exact A.Nf.i8 E S.labels (E.toFun a,w) (Or.inr hW)
end Be.IO.NR
namespace Be.JZ
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)} {mode: Bool}
def HG (base: Fin N ×Fin N→ ℕ) (A: JZ G M ell mode)
   (a: Fin A.NI.history.keys.card) (w: Fin N): ℕ:=
 if h:∃b,A.embed.toFun b=w then A.NY.result.labels (a,h.choose) else base (A.embed.toFun a,w)
def y8 (base: Fin N ×Fin N→ ℕ) (A: JZ G M ell mode)
   (S: tI G M ell): Prop:=
 ∀a,a∉A.view.Nm→∀w,S.labels (A.embed.toFun a,w)=base (A.embed.toFun a,w)
def Bc (base: Fin N ×Fin N→ ℕ) (A: JZ G M ell mode)
   (S: tI G M ell): Prop:=
 ∀a,a∉A.view.Nm→∀w,S.labels (A.embed.toFun a,w)=A.HG base a w
lemma Jk (base: Fin N ×Fin N→ ℕ) (A: JZ G M ell mode)
   (S: tI G M ell) (hA: A.Lj S) (hBefore: A.y8 base S):
   A.Bc base (A.next S hA):= by
 intro a ha w
 unfold HG
 split_ifs with hRange
 · have hMap:=A.NY.Kx hA.frame (a,hRange.choose) ha
   change (A.next S hA).labels (A.embed.toFun a,A.embed.toFun hRange.choose)=A.NY.result.labels (a,hRange.choose) at hMap
   rwa [hRange.choose_spec] at hMap
 · exact (A.NY.o7 hA.frame a w hRange).trans (hBefore a ha w)
lemma i5 (base: Fin N ×Fin N→ ℕ) (A: JZ G M ell mode)
   (S T: tI G M ell) (Y: Finset (Fin N)) (hA: A.Lj S)
   (hBefore: A.y8 base S) (h: Bl S T Y) (hDisjoint: Disjoint A.support Y):
   A.y8 base T:= by
 intro a ha w
 have hOutside: A.embed.toFun a∉Y:=fun hY=>disjoint_left.mp hDisjoint (hA.image a ha) hY
 exact (h.D6 (A.embed.toFun a,w) hOutside).trans (hBefore a ha w)
lemma kU (base: Fin N ×Fin N→ ℕ) (A: JZ G M ell mode)
   (S T: tI G M ell) (Y: Finset (Fin N)) (hA: A.M6 S)
   (hAfter: A.Bc base S) (h: Bl S T Y) (hDisjoint: Disjoint A.support Y):
   A.Bc base T:= by
 intro a ha w
 have hOutside: A.embed.toFun a∉Y:=fun hY=>disjoint_left.mp hDisjoint (hA.L1 a ha) hY
 exact (h.D6 (A.embed.toFun a,w) hOutside).trans (hAfter a ha w)
lemma f6 (as: List (JZ G M ell mode))
   (hPairs: as.Pairwise (fun A B=>Disjoint A.support B.support))
   (S: tI G M ell) (hAvail:∀A∈as,A.Lj S):
   ∃T,Dc mode (as.map LD) S T∧ Bl S T (MZ as)∧
     ∀A∈as,A.M6 T∧ A.Bc S.labels T:= by
 apply kF (y8 S.labels) (Bc S.labels)
   (Jk S.labels) (i5 S.labels) (kU S.labels) as hPairs S hAvail
 intro A hA a ha w
 rfl
end Be.JZ
end
noncomputable section
namespace Be.IO
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)} {S: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (D: IO) (h: Fi S ids hi out hOut data)
   (hD:∀z∈D,∃v,z=(ids v,data v)) (hClosed: D.history.JX)
def Ig (D: IO) (ids: Fin N→ ℕ): Finset (Fin N):=
 univ.filter (fun v=>ids v∈D.keys)
lemma JP (U: tI D.history.graph D.history.MG ell)
   (hView: D.view ell=some U) (F: Db (D.history.embedding (D.w7 h hD) hi hOut hClosed) U S)
   : Bh (D.history.embedding (D.w7 h hD) hi hOut hClosed) U (D.Ig ids) S:= by
 let A:=D.Ig ids
 have hCompatible:=D.Lf ell U hView
 have hImage:∀a,a∉U.Nm→((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun a∈A:=by
   intro a hA
   rw [hCompatible.Nm] at hA
   have hAlive: a∈D.alive:=by simpa using hA
   have hKey:=((D.Ls h hD hClosed a).mp hAlive).1
   have hID: ids (((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun a)=D.history.identity a:=D.history.yA (D.w7 h hD) a
   exact mem_filter.mpr ⟨mem_univ _,hID.symm ▸hKey⟩
 have hCover:∀r∈A,∀R,S.ND.state r=some R→
     ∃a Q,U.ND.state a=some Q∧((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun a=r:=by
   intro r hr R hR
   have hKey: ids r∈D.keys:=(mem_filter.mp hr).2
   obtain ⟨a,hID⟩:=D.history.rF (ids r) (D.rP hKey)
   have hAR:((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun a=r:=hi ((D.history.yA (D.w7 h hD) a).trans hID)
   have hAlive: a∈D.alive:=by
     apply (D.Ls h hD hClosed a).mpr
     refine ⟨hID.symm ▸hKey,?_⟩
     rw [hAR]
     exact S.vI r R hR
   obtain ⟨Q,hQ,hQR⟩:=D.Gv h hD hClosed a hAlive r R hR (by rw [hAR];exact R.tree.MU)
   exact ⟨Q.1,Q.2,(hCompatible.ND Q.1 Q.2).mpr hQ,hQR⟩
 refine ⟨F,hImage,?_,hCover⟩
 intro v hv hAlive
 have hKey: ids v∈D.keys:=(mem_filter.mp hv).2
 obtain ⟨a,hID⟩:=D.history.rF (ids v) (D.rP hKey)
 have hAV:((D.history.embedding (D.w7 h hD) hi hOut hClosed)).toFun a=v:=hi ((D.history.yA (D.w7 h hD) a).trans hID)
 refine ⟨a,?_,hAV⟩
 rw [hCompatible.Nm]
 have hLocalAlive: a∈D.alive:=(D.Ls h hD hClosed a).mpr
   ⟨hID.symm ▸hKey,by rw [hAV];exact hAlive⟩
 simpa only [mem_sdiff,mem_univ,true_and,not_not] using hLocalAlive
end Be.IO
end
noncomputable section
namespace Be
variable {N: ℕ}
def Mw (e: Sym2 (Fin N)): Fin N ×Fin N:=e.exists_rep.choose
lemma FI (e: Sym2 (Fin N)): s((Mw e).1,(Mw e).2)=e:=e.exists_rep.choose_spec
namespace tE
variable {G: SimpleGraph (Fin N)} {s: ℕ} (P: tE G s)
def ET (e: Sym2 (Fin N)): Finset (Fin N):=P.FE e.toFinset
def ES {I: Type} (ids: Fin N→ ℕ) (data: Fin N→ I) (e: Sym2 (Fin N)): Nw I:=
 (P.ET e).image (fun v=>(ids v,data v))
lemma vX (e: Sym2 (Fin N)) (v: Fin N): v∈P.ET e↔ P.leader v∈e:= by
 simp only [ET,xN,Sym2.mem_toFinset]
lemma jL (R H: SimpleGraph (Fin N)) (hR: Matching H R)
   (e f: R.edgeSet) (hEF: e≠f): Disjoint (P.ET e.val) (P.ET f.val):= by
 apply disjoint_left.mpr
 intro v hv hw
 exact hR.2 e (mem_univ _) f (mem_univ _) hEF (P.leader v)
   ((P.vX e.val v).mp hv) ((P.vX f.val v).mp hw)
lemma g9 (e: Sym2 (Fin N)) (u: Fin N) (hu: u∈P.ET e)
   (v: Fin N) (hUV: P.leader v=P.leader u): v∈P.ET e:= by
 apply (P.vX e v).mpr
 rw [hUV]
 exact (P.vX e u).mp hu
lemma nV (e: Sym2 (Fin N)):
   P.ET e=(univ.filter (fun v=>P.leader v=(Mw e).1))∪
     (univ.filter (fun v=>P.leader v=(Mw e).2)):= by
 ext v
 rw [P.vX]
 conv_lhs=> rw [←FI e]
 simp only [Sym2.mem_iff,mem_union,mem_filter,mem_univ,true_and]
lemma nU {I: Type} (ids: Fin N→ ℕ) (data: Fin N→ I)
   (e: Sym2 (Fin N)) (hLeft: P.leader (Mw e).1=(Mw e).1)
   (hRight: P.leader (Mw e).2=(Mw e).2):
   P.ES ids data e=P.NI ids data (Mw e).1∪P.NI ids data (Mw e).2:= by
 rw [ES,P.nV,image_union]
 simp only [NI,hLeft,hRight]
end tE
end Be
end
noncomputable section
namespace Be.IO
variable {N: ℕ}
def MM (X: Finset (Fin N)) (ids: Fin N→ ℕ) (data: Fin N→ Ln): IO:=
 X.image (fun v=>(ids v,data v))
lemma u2 (X: Finset (Fin N)) (ids: Fin N→ ℕ) (data: Fin N→ Ln):
   ∀z∈MM X ids data,∃v,z=(ids v,data v):= by
 intro z hz
 obtain ⟨v,hV,hEq⟩:=mem_image.mp hz
 exact ⟨v,hEq.symm⟩
lemma Ib (X: Finset (Fin N)) (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (data: Fin N→ Ln) (v: Fin N): ids v∈(MM X ids data).keys↔ v∈X:= by
 unfold keys MM
 rw [image_image]
 constructor
 · intro h
   obtain ⟨w,hw,hEq⟩:=mem_image.mp h
   have hWV: w=v:=hi hEq
   exact hWV ▸hw
 · intro h
   exact mem_image.mpr ⟨v,h,rfl⟩
lemma nF (X: Finset (Fin N)) (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (data: Fin N→ Ln):(MM X ids data).Ig ids=X:= by
 ext v
 simp only [Ig,mem_filter,mem_univ,true_and,Ib X ids hi data v]
lemma u3 {size: ℕ} {G: SimpleGraph (Fin N)} (P: tE G size)
   (X: Finset (Fin N)) (ids: Fin N→ ℕ) (hi: Function.Injective ids) (data: Fin N→ Ln)
   (hX:∀u∈X,∀v,P.leader v=P.leader u→ v∈X):
   (MM X ids data).Saturated P ids:= by
 intro u hu v hVU
 exact (Ib X ids hi data v).mpr (hX u ((Ib X ids hi data u).mp hu) v hVU)
end Be.IO
namespace Be.tE
variable {N size: ℕ} {G: SimpleGraph (Fin N)} (P: tE G size)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (data: Fin N→ Ln)
include hi
lemma g8 (e: Sym2 (Fin N)):
   IO.Saturated (P.ES ids data e) P ids:=
 IO.u3 P (P.ET e) ids hi data (P.g9 e)
lemma dD (e: Sym2 (Fin N)):
   IO.Ig (P.ES ids data e) ids=P.ET e:=
 IO.nF (P.ET e) ids hi data
end Be.tE
end
noncomputable section
namespace Be.tE
variable {N size: ℕ} {G: SimpleGraph (Fin N)} (P: tE G size)
   (Lx: Fin N→ Fin N→ Prop) (hC: Symmetric Lx)
   (R: SimpleGraph (Fin N)) (hR: Matching (P.Lv Lx hC) R)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids)
include hR
lemma vY (e: R.edgeSet):
   P.leader (Mw e.val).1=(Mw e.val).1∧
   P.leader (Mw e.val).2=(Mw e.val).2∧
   R.Adj (Mw e.val).1 (Mw e.val).2:= by
 have hEdge: R.Adj (Mw e.val).1 (Mw e.val).2:=R.mem_edgeSet.mp (by rw [FI];exact e.property)
 have hAux:=hR.1 hEdge
 exact ⟨hAux.1,hAux.2.1,hEdge⟩
lemma AS (e: R.edgeSet):
   Ni ids hi R (Mw e.val).1=(Mw e.val).2:= by
 unfold Ni
 rw [(tB.LW ids hi R
   (qJ.gP _ R hR) _ _).mpr (P.vY Lx hC R hR e).2.2]
 rfl
lemma c7 (e: R.edgeSet):
   (univ.filter (fun w=>P.HY R ids hi w=P.HY R ids hi (Mw e.val).1))=
     P.ET e.val:= by
 have hEnds:=P.vY Lx hC R hR e
 have hPartner:=P.AS Lx hC R hR ids hi e
 have hInv:=vA ids hi R (qJ.gP _ R hR)
 ext w
 simp only [mem_filter,mem_univ,true_and,P.vX]
 change representative ids (Ni ids hi R) (P.leader w)=
   representative ids (Ni ids hi R) (P.leader (Mw e.val).1)↔ _
 rw [hEnds.1,eq_comm,yI ids hi _ hInv,hPartner]
 conv_rhs=> rw [←FI e.val]
 simp only [Sym2.mem_iff]
lemma k2 {I: Type} (data: Fin N→ I) (e: R.edgeSet) (v: Fin N)
   (hv: v∈P.ET e.val):
   (univ.filter (fun w=>P.HY R ids hi w=P.HY R ids hi v)).image
     (fun w=>(ids w,data w))=P.ES ids data e.val:= by
 have hBlock:=P.c7 Lx hC R hR ids hi e
 have hMem: v∈univ.filter (fun w=>P.HY R ids hi w=P.HY R ids hi (Mw e.val).1):=hBlock.symm ▸hv
 have hV: P.HY R ids hi v=P.HY R ids hi (Mw e.val).1:=
   (mem_filter.mp hMem).2
 rw [hV,hBlock]
 rfl
end Be.tE
end
noncomputable section
namespace Be
structure qI {N ell: ℕ} {G M: SimpleGraph (Fin N)}
   (D: IO) (X: Finset (Fin N)) (S: tI G M ell) (mode: Bool)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (out: Fin N→ Option ℕ)
   (hOut: ReportsMatching G ids out M) (hAuth: D.history.Li G ids out) (external: Bool) where
 closed: D.history.JX
 NA: IO.JR D ell mode external
 Lz: D.Kc ell mode external=some NA
 region: Bh (D.history.embedding hAuth hi hOut closed) NA.state X S
namespace qI
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)} {D: IO} {X: Finset (Fin N)}
   {S: tI G M ell} {mode: Bool} {ids: Fin N→ ℕ} {hi: Function.Injective ids}
   {out: Fin N→ Option ℕ} {hOut: ReportsMatching G ids out M} {hAuth: D.history.Li G ids out} {external: Bool}
   (A: qI D X S mode ids hi out hOut hAuth external)
def task: JZ G M ell mode:=
 ⟨D,A.NA.state,D.history.embedding hAuth hi hOut A.closed,X,A.NA.tail,A.NA.head,A.NA.NY⟩
lemma Lw: A.task.Lj S:=A.region
end qI
end Be
end
noncomputable section
namespace Be.IO
variable (D: IO) (hConsistent: D.history.JS) (hClosed: D.history.JX)
   {ell: ℕ} {mode external: Bool} (W: JR D ell mode external)
lemma zL (hW: D.Kc ell mode external=some W)
   (a: Fin D.history.keys.card) (old: Ln):
   D.Lt ell mode external (D.history.identity a) old=
     D.JO hConsistent hClosed W.NY.result a old:= by
 unfold Lt
 rw [dif_pos hConsistent,dif_pos hClosed,hW]
 dsimp only
 have hIndex:∃b,D.history.identity b=D.history.identity a:=⟨a,rfl⟩
 rw [dif_pos hIndex]
 rw [D.history.identity_injective hIndex.choose_spec]
variable (U: tI D.history.graph D.history.MG ell)
lemma v5 (a: Fin D.history.keys.card) (old: Ln):
   (D.JO hConsistent hClosed U a old).neighbors=old.neighbors∧
   (D.JO hConsistent hClosed U a old).Jf=old.Jf∧
   (D.JO hConsistent hClosed U a old).ignored=old.ignored:= by
 unfold JO
 split_ifs<;> exact ⟨rfl,rfl,rfl⟩
lemma s6 (a: Fin D.history.keys.card) (old: Ln) (hOld: old.Nm=false):
   (D.JO hConsistent hClosed U a old).Nm=true↔ a∈U.Nm:= by
 simp only [JO,hOld,Bool.false_eq_true,if_false,decide_eq_true_eq]
lemma y3 (a: Fin D.history.keys.card) (old: Ln) (hOld: old.Nm=false):
   (D.JO hConsistent hClosed U a old).Md=D.KM U a:= by
 simp only [JO,hOld,Bool.false_eq_true,if_false]
lemma y2 (a: Fin D.history.keys.card) (old: Ln) (hOld: old.Nm=false):
   (D.JO hConsistent hClosed U a old).L8=D.JD hConsistent hClosed U a:= by
 simp only [JO,hOld,Bool.false_eq_true,if_false]
lemma jU (a: Fin D.history.keys.card) (old: Ln) (hOld: old.Nm=true):
   D.JO hConsistent hClosed U a old=old:= by
 simp only [JO,hOld,if_true]
lemma zM (ell: ℕ) (mode external: Bool) (j: ℕ) (old: Ln):
   (D.Lt ell mode external j old).neighbors=old.neighbors∧
   (D.Lt ell mode external j old).Jf=old.Jf∧
   (D.Lt ell mode external j old).ignored=old.ignored:= by
 by_cases hC: D.history.JS
 · simp only [Lt,dif_pos hC]
   by_cases hM: D.history.JX
   · simp only [dif_pos hM]
     cases hChoice: D.Kc ell mode external with
     | none => simp
     | some W =>
       dsimp only
       by_cases hIndex:∃a,D.history.identity a=j
       · simp only [dif_pos hIndex]
         exact D.v5 hC hM W.NY.result hIndex.choose old
       · simp only [dif_neg hIndex]
         simp
   · simp only [dif_neg hM]
     simp
 · simp only [Lt,dif_neg hC]
   simp
lemma l7 (ell: ℕ) (mode external: Bool) (j: ℕ) (old: Ln) (hOld: old.Nm=true):
   D.Lt ell mode external j old=old:= by
 by_cases hC: D.history.JS
 · simp only [Lt,dif_pos hC]
   by_cases hM: D.history.JX
   · simp only [dif_pos hM]
     cases hChoice: D.Kc ell mode external with
     | none => rfl
     | some W =>
       dsimp only
       by_cases hIndex:∃a,D.history.identity a=j
       · simp only [dif_pos hIndex]
         exact D.jU hC hM W.NY.result hIndex.choose old hOld
       · simp only [dif_neg hIndex]
   · simp only [dif_neg hM]
 · simp only [Lt,dif_neg hC]
end Be.IO
end
noncomputable section
namespace Be.IO
variable (D: IO) (hConsistent: D.history.JS) (hClosed: D.history.JX) {ell: ℕ}
   (U: tI D.history.graph D.history.MG ell)
   {N: ℕ} {G M: SimpleGraph (Fin N)}
   (E: wF D.history.graph D.history.MG G M)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (hIDs:∀a,ids (E.toFun a)=D.history.identity a)
include hi hIDs in
lemma eO (base: Fin N ×Fin N→ ℕ) (a: Fin D.history.keys.card)
   (old: Ln) (hOld: old.Nm=false)
   (hBase:∀w,old.labels (ids w)=base (E.toFun a,w)) (w: Fin N):
   (D.JO hConsistent hClosed U a old).labels (ids w)=
     if h:∃b,E.toFun b=w then U.labels (a,h.choose) else base (E.toFun a,w):= by
 unfold JO
 rw [hOld]
 simp only [Bool.false_eq_true,if_false]
 by_cases hRange:∃b,E.toFun b=w
 · have hNat:∃b,D.history.identity b=ids w:=by
     obtain ⟨b,hB⟩:=hRange
     exact ⟨b,(hIDs b).symm.trans (congrArg ids hB)⟩
   rw [dif_pos hNat,dif_pos hRange]
   have hChoice: E.toFun hNat.choose=w:=hi ((hIDs hNat.choose).trans hNat.choose_spec)
   have hEq: hNat.choose=hRange.choose:=E.injective (hChoice.trans hRange.choose_spec.symm)
   rw [hEq]
 · have hNat:¬∃b,D.history.identity b=ids w:=by
     rintro ⟨b,hB⟩
     exact hRange ⟨b,hi ((hIDs b).trans hB)⟩
   rw [dif_neg hNat,dif_neg hRange]
   exact hBase w
end Be.IO
end
noncomputable section
namespace Be.qI
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)} {D: IO} {X: Finset (Fin N)}
   {S: tI G M ell} {mode: Bool} {ids: Fin N→ ℕ} {hi: Function.Injective ids}
   {out: Fin N→ Option ℕ} {hOut: ReportsMatching G ids out M} {hAuth: D.history.Li G ids out} {external: Bool}
   (A: qI D X S mode ids hi out hOut hAuth external)
lemma Mz (a: Fin D.history.keys.card): ids (A.task.embed.toFun a)=D.history.identity a:=
 D.history.yA hAuth a
lemma decode (a: Fin D.history.keys.card) (old: Ln):
   D.Lt ell mode external (D.history.identity a) old=
     D.JO (D.history.oF hi hAuth) A.closed A.NA.NY.result a old:=
 D.zL (D.history.oF hi hAuth) A.closed A.NA A.Lz a old
lemma FF (base: Fin N ×Fin N→ ℕ) (a: Fin D.history.keys.card) (old: Ln)
   (hOld: old.Nm=false) (hBase:∀w,old.labels (ids w)=base (A.task.embed.toFun a,w)) (w: Fin N):
   (D.Lt ell mode external (D.history.identity a) old).labels (ids w)=A.task.HG base a w:= by
 rw [A.decode]
 exact D.eO (D.history.oF hi hAuth) A.closed
   A.NA.NY.result A.task.embed ids hi A.Mz base a old hOld hBase w
lemma Dx (a: Fin D.history.keys.card) (old: Ln) (hOld: old.Nm=false):
   (D.Lt ell mode external (D.history.identity a) old).Nm=true↔ a∈A.NA.NY.result.Nm:= by
 rw [A.decode]
 exact D.s6 _ _ _ a old hOld
lemma Hp (a: Fin D.history.keys.card) (old: Ln) (hOld: old.Nm=false):
   (D.Lt ell mode external (D.history.identity a) old).L8=
     D.JD (D.history.oF hi hAuth) A.closed A.NA.NY.result a:= by
 rw [A.decode]
 exact D.y2 _ _ _ a old hOld
end Be.qI
end
noncomputable section
namespace Be.Fi
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)} {S T: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (h: Fi S ids hi out hOut data)
include h
lemma CY (v: Fin N) (hV: v∉S.Nm):(data v).Nm=false:= by
 cases hb:(data v).Nm with
 | false => rfl
 | true => exact (hV ((h.Nm v).mp hb)).elim
lemma vO (v: Fin N) (hV: v∈S.Nm):(data v).L8=none:= by
 cases hA:(data v).L8 with
 | none => rfl
 | some A =>
   obtain ⟨hRep,hMember⟩:=h.Jr v A hA
   obtain ⟨r,hID,R,hR,hVR⟩:=A.sP S ids hi out hOut hRep v hMember
   exact (S.k7 r R hR v hVR hV).elim
lemma jA {X: Finset (Fin N)} (hStep: Bl S T X)
   (v: Fin N) (hV: v∉X) (A: tF) (hA:(data v).L8=some A):
   A.Represents T ids hi out hOut∧ ids v∈A.members:= by
 obtain ⟨hRep,hMember⟩:=h.Jr v A hA
 refine ⟨?_,hMember⟩
 obtain ⟨hAuth,hState⟩:=hRep
 refine ⟨hAuth,?_⟩
 let E:=A.history.embedding hAuth hi hOut A.KB
 have hContains: v∈(A.state.Nd E).tree.vertices:=by
   obtain ⟨a,ha,hID⟩:=mem_image.mp hMember
   have hAV: E.toFun a=v:=hi ((A.history.yA hAuth a).trans hID)
   rw [A.state.Aj E]
   exact mem_image.mpr ⟨a,ha,hAV⟩
 have hRoot: E.toFun A.root∉X:=fun hr=>hV (hStep.AB _ hr _ hState hContains)
 exact (hStep.DO _ hRoot).trans hState
end Be.Fi
namespace Be.JZ
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)} {mode: Bool}
lemma HV (as: List (JZ G M ell mode)) (v: Fin N):
   v∈MZ as↔∃A∈as,v∈A.support:= by
 induction as with
 | nil => simp [MZ]
 | cons A as ih =>
   simp only [MZ,mem_union,ih,List.mem_cons]
   constructor
   · rintro (h|⟨B,hB,hV⟩)
     · exact ⟨A,Or.inl rfl,h⟩
     · exact ⟨B,Or.inr hB,hV⟩
   · rintro ⟨B,hB,hV⟩
     rcases hB with hB|hB
     · subst B;exact Or.inl hV
     · exact Or.inr ⟨B,hB,hV⟩
end Be.JZ
end
noncomputable section
namespace Be
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)}
namespace qF
variable {S: tI G M ell} {x y: Fin N}
lemma DR (R: qF S x y) (u: Fin N) (hu: u∈R.MD.support): u∉S.Nm:= by
 have hSupport: R.MD.support⊆R.left.tree.vertices∪R.right.tree.vertices:=
   R.left.tree.cR R.right.tree _ _ R.M1 R.head_mem R.path
 rcases mem_union.mp (hSupport hu) with hU|hU
 · exact S.k7 _ _ R.HJ u hU
 · exact S.k7 _ _ R.GE u hU
end qF
namespace M3
variable {S T: tI G M ell} {mode: Bool} {x y: Fin N}
lemma u5 (h: M3 mode x y S T) (u v: Fin N) (hU: u∈S.Nm):
   T.Et.Adj u v↔ S.Et.Adj u v:= by
 cases h with
 | augmentation R hFlag => exact R.k6 u v (fun hu=>R.DR u hu hU)
 | extension hMode R hNo A => cases A<;> rfl
 | skip hNo hNoExt => rfl
lemma uH (h: M3 mode x y S T) (u v: Fin N) (hU: u∈S.Nm):
   T.labels (u,v)=S.labels (u,v):= by
 cases h with
 | augmentation R hFlag => rfl
 | extension hMode R hNo A => exact A.gK (u,v) (Or.inl hU)
 | skip hNo hNoExt => rfl
lemma F7 (h: M3 mode x y S T) (u v: Fin N):
   T.NV.Adj u v↔ S.NV.Adj u v∧ u∉T.Nm∧ v∉T.Nm:= by
 constructor
 · intro hEdge
   exact ⟨h.MF hEdge,T.HK u v hEdge⟩
 · rintro ⟨hEdge,hu,hv⟩
   cases h with
   | augmentation R hFlag => exact ⟨hEdge,fun hD=>hu (mem_union_right _ hD),fun hD=>hv (mem_union_right _ hD)⟩
   | extension hMode R hNo A => cases A<;> exact hEdge
   | skip hNo hNoExt => exact hEdge
end M3
namespace M2
variable {S T: tI G M ell} {mode: Bool} {es: List (Fin N ×Fin N)}
lemma u5 (h: M2 mode es S T) (u v: Fin N) (hU: u∈S.Nm):
   T.Et.Adj u v↔ S.Et.Adj u v:= by
 induction h with
 | nil => rfl
 | cons step rest ih => exact (ih (step.In hU)).trans (step.u5 u v hU)
lemma uH (h: M2 mode es S T) (u v: Fin N) (hU: u∈S.Nm):
   T.labels (u,v)=S.labels (u,v):= by
 induction h with
 | nil => rfl
 | cons step rest ih => exact (ih (step.In hU)).trans (step.uH u v hU)
lemma F7 (h: M2 mode es S T) (u v: Fin N):
   T.NV.Adj u v↔ S.NV.Adj u v∧ u∉T.Nm∧ v∉T.Nm:= by
 induction h with
 | nil S =>
   exact ⟨fun hEdge=>⟨hEdge,S.HK u v hEdge⟩,And.left⟩
 | @cons x y es S V T step rest ih =>
   constructor
   · intro hEdge
     exact ⟨step.MF (rest.MF hEdge),T.HK u v hEdge⟩
   · rintro ⟨hEdge,hu,hv⟩
     apply ih.mpr
     refine ⟨?_,hu,hv⟩
     exact (step.F7 u v).mpr ⟨hEdge,fun hU=>hu (rest.In hU),fun hV=>hv (rest.In hV)⟩
end M2
end Be
end
noncomputable section
namespace Be.IO
variable (D: IO) (hConsistent: D.history.JS) (hClosed: D.history.JX) {ell: ℕ}
   (S: tI D.history.graph D.history.MG ell)
lemma AP (u: Fin D.history.keys.card) (A: tF)
   (hA: D.JD hConsistent hClosed S u=some A):
   ∃(r: Fin D.history.keys.card) (R: Lp D.history.graph D.history.MG r),
     ∃hR: S.ND.state r=some R,u∈R.tree.vertices∧
     A=⟨D.history,hConsistent,hClosed,r,R,S.complete r R hR⟩:= by
 unfold JD at hA
 obtain ⟨r,hOwner,hModel⟩:=Option.bind_eq_some_iff.mp hA
 obtain ⟨R,hR,hU⟩:=(S.ND.KP r u).mp hOwner
 rw [D.yM hConsistent hClosed S r R hR] at hModel
 exact ⟨r,R,hR,hU,(Option.some.inj hModel).symm⟩
variable {N: ℕ} {G M: SimpleGraph (Fin N)} (T: tI G M ell)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (out: Fin N→ Option ℕ)
   (hOut: ReportsMatching G ids out M) (hAuth: D.history.Li G ids out)
lemma lI
   (hMap: G8.Mr (D.history.embedding hAuth hi hOut hClosed) S.ND T.ND)
   (u: Fin D.history.keys.card) (A: tF)
   (hA: D.JD hConsistent hClosed S u=some A):
   A.Represents T ids hi out hOut∧ D.history.identity u∈A.members:= by
 obtain ⟨r,R,hR,hU,hEq⟩:=D.AP hConsistent hClosed S u A hA
 subst A
 constructor
 · exact ⟨hAuth,hMap r R hR⟩
 · exact mem_image.mpr ⟨u,hU,rfl⟩
end Be.IO
end
noncomputable section
namespace Be
variable {N: ℕ} {G J K: SimpleGraph (Fin N)} {ids: Fin N→ ℕ}
   {out out': Fin N→ Option ℕ}
lemma CA (h: ReportsMatching G ids out J) (h': ReportsMatching G ids out' K)
   (u: Fin N) (hEdges:∀v,J.Adj u v↔ K.Adj u v): out u=out' u:= by
 cases hU: out u with
 | none =>
   have hFree:=(h.2 u).1.mp hU
   have hFree':∀v,¬K.Adj u v:=fun v hEdge=>hFree v ((hEdges v).mpr hEdge)
   exact ((h'.2 u).1.mpr hFree').symm
 | some j =>
   obtain ⟨v,hV,hID⟩:=(h.2 u).2 j|>.mp hU
   exact ((h'.2 u).2 j|>.mpr ⟨v,(hEdges v).mp hV,hID⟩).symm
end Be
end
noncomputable section
namespace Be
structure wE {N ell: ℕ} {G M: SimpleGraph (Fin N)}
   (S: tI G M ell) (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (out: Fin N→ Option ℕ) (hOut: ReportsMatching G ids out M) (data: Fin N→ Ln)
   (mode external: Bool) (ι: Type) where
 NI: ι→ IO
 region: ι→ Finset (Fin N)
 Lu:∀i,(NI i).history.Li G ids out
 Na:∀i,qI (NI i) (region i) S mode ids hi out hOut (Lu i) external
 disjoint:∀i j,i≠j→ Disjoint (region i) (region j)
 NQ:∀i r V,S.ND.state r=some V→∀v∈V.tree.vertices,(v∈region i↔ r∈region i)
namespace wE
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)} {S T: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   {mode external: Bool} {ι: Type} [Fintype ι]
   (F: wE S ids hi out hOut data mode external ι)
def update (v: Fin N): Ln:=
 if h:∃i,v∈F.region i then
   (F.NI h.choose).Lt ell mode external (ids v) (data v)
 else data v
lemma Mj (i: ι) (v: Fin N) (hV: v∈F.region i):
   F.update v=(F.NI i).Lt ell mode external (ids v) (data v):= by
 unfold update
 have h:∃j,v∈F.region j:=⟨i,hV⟩
 rw [dif_pos h]
 have hh: h.choose=i:=by
   by_contra hn
   exact disjoint_left.mp (F.disjoint h.choose i hn) h.choose_spec hV
 rw [hh]
lemma E4 (v: Fin N) (hV:∀i,v∉F.region i): F.update v=data v:= by
 unfold update
 rw [dif_neg (by simpa only [not_exists] using hV)]
lemma GX (v: Fin N):(F.update v).neighbors=(data v).neighbors∧
   (F.update v).Jf=(data v).Jf∧(F.update v).ignored=(data v).ignored:= by
 unfold update
 split_ifs with hh
 · exact IO.zM _ ell mode external (ids v) (data v)
 · exact ⟨rfl,rfl,rfl⟩
lemma v4 (v: Fin N) (hV:(data v).Nm=true): F.update v=data v:= by
 unfold update
 split_ifs with hh
 · exact IO.l7 _ ell mode external (ids v) (data v) hV
 · rfl
def tasks: List (JZ G M ell mode):=
 (univ: Finset ι).toList.map (fun i=>(F.Na i).task)
structure Witness (T: tI G M ell): Prop where
 pass:∃es,Dc mode es S T
 support: Bl S T (JZ.MZ F.tasks)
 MO:∀i,(F.Na i).task.M6 T∧(F.Na i).task.Bc S.labels T
lemma E6:∃T,F.Witness T:= by
 have hPairs: F.tasks.Pairwise (fun A B=>Disjoint A.support B.support):=by
   apply List.pairwise_map.mpr
   apply (Finset.nodup_toList (univ: Finset ι)).imp
   intro i j hNe
   exact F.disjoint i j hNe
 obtain ⟨T,hPass,hSupport,hOutcomes⟩:=JZ.f6 F.tasks hPairs S (by
   intro A hA
   obtain ⟨i,hi,hEq⟩:=List.mem_map.mp hA
   subst A
   exact (F.Na i).Lw)
 exact ⟨T,⟨⟨_,hPass⟩,hSupport,fun i=>hOutcomes _ (List.mem_map.mpr
   ⟨i,Finset.mem_toList.mpr (mem_univ _),rfl⟩)⟩⟩
lemma HV (v: Fin N): v∈JZ.MZ F.tasks↔∃i,v∈F.region i:= by
 rw [JZ.HV]
 constructor
 · rintro ⟨A,hA,hVA⟩
   obtain ⟨i,hi,hEq⟩:=List.mem_map.mp hA
   subst A
   exact ⟨i,hVA⟩
 · rintro ⟨i,hi⟩
   exact ⟨(F.Na i).task,List.mem_map.mpr ⟨i,Finset.mem_toList.mpr (mem_univ _),rfl⟩,hi⟩
end wE
end Be
end
noncomputable section
namespace Be.wE
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)} {S T: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   {mode external: Bool} {ι: Type} [Fintype ι]
   (F: wE S ids hi out hOut data mode external ι)
   (h: Fi S ids hi out hOut data) (W: F.Witness T)
include W in
lemma Witness.M9:∃es,M2 mode es S T:= by
 obtain ⟨es,hp⟩:=W.pass
 exact ⟨es,hp.Mh⟩
include W h in
lemma Hh (u w: Fin N):
   (F.update u).labels (ids w)=T.labels (u,w):= by
 by_cases hOld: u∈S.Nm
 · rw [F.v4 u ((h.Nm u).mpr hOld),h.labels]
   obtain ⟨es,hPass⟩:=W.M9
   exact (hPass.uH u w hOld).symm
 · by_cases hSel:∃e: ι,u∈F.region e
   · obtain ⟨e,he⟩:=hSel
     let A:=F.Na e
     obtain ⟨a,ha,hAU⟩:=A.region.IV u he hOld
     change A.task.embed.toFun a=u at hAU
     have hID: A.task.NI.history.identity a=ids u:=
       (A.Mz a).symm.trans (congrArg ids hAU)
     rw [F.Mj e u he,←hID]
     have hd:=A.FF S.labels a (data u) (h.CY u hOld)
       (fun v=>by rw [h.labels,hAU]) w
     have hh: T.labels (A.task.embed.toFun a,w)=A.task.HG S.labels a w:=
       (W.MO e).2 a ha w
     rw [hAU] at hh
     exact hd.trans hh.symm
   · have hOutside: u∉JZ.MZ (F.tasks):=
       fun hh=>hSel ((F.HV u).mp hh)
     rw [F.E4 u (by simpa only [not_exists] using hSel),h.labels]
     exact (W.support.D6 (u,w) hOutside).symm
include W h in
lemma Fx (u: Fin N):
   (F.update u).Nm=true↔ u∈T.Nm:= by
 by_cases hOld: u∈S.Nm
 · have hNew: u∈T.Nm:=by obtain ⟨es,hPass⟩:=W.M9;exact hPass.In hOld
   rw [F.v4 u ((h.Nm u).mpr hOld)]
   exact ⟨fun _=>hNew,fun _=>(h.Nm u).mpr hOld⟩
 · by_cases hSel:∃e: ι,u∈F.region e
   · obtain ⟨e,he⟩:=hSel
     let A:=F.Na e
     obtain ⟨a,ha,hAU⟩:=A.region.IV u he hOld
     change A.task.embed.toFun a=u at hAU
     have hID: A.task.NI.history.identity a=ids u:=
       (A.Mz a).symm.trans (congrArg ids hAU)
     rw [F.Mj e u he,←hID]
     have hh: a∈A.NA.NY.result.Nm↔ A.task.embed.toFun a∈T.Nm:=
       (W.MO e).1.Nm a ha
     rw [hAU] at hh
     exact (A.Dx a (data u) (h.CY u hOld)).trans hh
   · have hOutside: u∉JZ.MZ (F.tasks):=
       fun hh=>hSel ((F.HV u).mp hh)
     rw [F.E4 u (by simpa only [not_exists] using hSel)]
     exact (h.Nm u).trans (W.support.Cy u hOutside).symm
include W h in
lemma mE (u: Fin N) (hu: u∉T.Nm):
   (F.update u).Nm=false:= by
 cases hb:(F.update u).Nm with
 | false => rfl
 | true => exact (hu ((F.Fx h W u).mp hb)).elim
end Be.wE
end
noncomputable section
namespace Be.wE
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)} {S T: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   {mode external: Bool} {ι: Type} [Fintype ι]
   (F: wE S ids hi out hOut data mode external ι)
   (h: Fi S ids hi out hOut data) (W: F.Witness T)
include W h in
lemma J8 (u v: Fin N):
   T.NV.Adj u v↔ G.Adj u v∧
     (F.update u).Nm=false∧
     (F.update v).Nm=false∧
     ids v∉(F.update u).ignored∧
     ids u∉(F.update v).ignored:= by
 obtain ⟨es,hPass⟩:=W.M9
 rw [(F.GX u).2.2,
   (F.GX v).2.2]
 constructor
 · intro hEdge
   have hOld:=(h.NV u v).mp (hPass.MF hEdge)
   have hAlive:=T.HK u v hEdge
   exact ⟨hOld.1,F.mE h W u hAlive.1,
     F.mE h W v hAlive.2,hOld.2.2.2⟩
 · rintro ⟨hEdge,hu,hv,hUV,hVU⟩
   have hU: u∉T.Nm:=by
     intro hh
     have hh':=(F.Fx h W u).mpr hh
     rw [hu] at hh'
     cases hh'
   have hV: v∉T.Nm:=by
     intro hh
     have hh':=(F.Fx h W v).mpr hh
     rw [hv] at hh'
     cases hh'
   exact (hPass.F7 u v).mpr ⟨(h.NV u v).mpr ⟨hEdge,
     h.CY u (fun hh=>hU (hPass.In hh)),
     h.CY v (fun hh=>hV (hPass.In hh)),hUV,hVU⟩,hU,hV⟩
include W h in
lemma wM (u: Fin N) (B: tF)
   (hB:(F.update u).L8=some B):
   B.Represents T ids hi out hOut∧ ids u∈B.members:= by
 by_cases hOld: u∈S.Nm
 · rw [F.v4 u ((h.Nm u).mpr hOld),
     h.vO u hOld] at hB
   cases hB
 · by_cases hSel:∃e: ι,u∈F.region e
   · obtain ⟨e,he⟩:=hSel
     let A:=F.Na e
     obtain ⟨a,ha,hAU⟩:=A.region.IV u he hOld
     change A.task.embed.toFun a=u at hAU
     have hID: A.task.NI.history.identity a=ids u:=
       (A.Mz a).symm.trans (congrArg ids hAU)
     rw [F.Mj e u he,←hID] at hB
     have hBM:=(A.Hp a (data u) (h.CY u hOld)).symm.trans hB
     have hAuth: A.task.NI.history.Li G ids out:=F.Lu e
     have hh:=A.task.NI.lI
       (A.task.NI.history.oF hi hAuth) A.closed A.NA.NY.result T ids hi out hOut hAuth
       (W.MO e).1.region.frame.present a B hBM
     exact ⟨hh.1,by simpa only [hID] using hh.2⟩
   · have hOutside: u∉JZ.MZ (F.tasks):=
       fun hh=>hSel ((F.HV u).mp hh)
     rw [F.E4 u (by simpa only [not_exists] using hSel)] at hB
     exact h.jA W.support u hOutside B hB
end Be.wE
end
noncomputable section
namespace Be.wE
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)} {S T: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   {mode external: Bool} {ι: Type} [Fintype ι]
   (F: wE S ids hi out hOut data mode external ι)
   (h: Fi S ids hi out hOut data) (W: F.Witness T)
include W h in
lemma Hi: ReportsMatching G ids
   (fun v=>let node:=F.update v
     if node.Nm then node.Md else node.Jf) T.Et:= by
 have hCanon:=tB.uZ G T.Et ids hi T.Eu.1.1
   (qJ.gP _ _ T.Eu.1)
 have hEq:(fun v=>let node:=F.update v
     if node.Nm then node.Md else node.Jf)=
     (fun v=>(tB.NW ids hi T.Et v).map ids):=by
   funext v
   dsimp only
   obtain ⟨es,hPass⟩:=W.M9
   by_cases hNew: v∈T.Nm
   · rw [(F.Fx h W v).mpr hNew,if_pos rfl]
     by_cases hOld: v∈S.Nm
     · rw [F.v4 v ((h.Nm v).mpr hOld)]
       have hh:=CA h.output hCanon v (fun w=>(hPass.u5 v w hOld).symm)
       simpa only [(h.Nm v).mpr hOld,if_true] using hh
     · have hSel:∃e: ι,v∈F.region e:=by
         by_contra hh
         have hOutside: v∉JZ.MZ (F.tasks):=
           fun hv=>hh ((F.HV v).mp hv)
         exact hOld ((W.support.Cy v hOutside).mp hNew)
       obtain ⟨e,he⟩:=hSel
       let A:=F.Na e
       obtain ⟨a,ha,hAV⟩:=A.region.IV v he hOld
       change A.task.embed.toFun a=v at hAV
       have hID: A.task.NI.history.identity a=ids v:=
         (A.Mz a).symm.trans (congrArg ids hAV)
       rw [F.Mj e v he,←hID]
       refine (congrArg Ln.Md (A.decode a (data v))).trans ?_
       refine (IO.y3 _ _ _ _ a (data v) (h.CY v hOld)).trans ?_
       have hh:=(W.MO e).1.Jv ids A.Mz _ hCanon a ha
       change A.task.NI.KM A.NA.NY.result a=
         (tB.NW ids hi T.Et (A.task.embed.toFun a)).map ids at hh
       rw [hAV] at hh
       exact hh
   · rw [F.mE h W v hNew]
     simp only [Bool.false_eq_true,if_false]
     rw [(F.GX v).2.1,h.Jf]
     exact CA hOut hCanon v (fun w=>(T.Cp v w hNew).symm)
 rw [hEq]
 exact hCanon
end Be.wE
end
noncomputable section
namespace Be.wE
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)} {S T: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   {mode external: Bool} {ι: Type} [Fintype ι]
   (F: wE S ids hi out hOut data mode external ι)
   (h: Fi S ids hi out hOut data) (W: F.Witness T)
include W h in
lemma oG (r: Fin N) (V: Lp G M r) (hV: T.ND.state r=some V):
   ∃B,∀v∈V.tree.vertices,
     (F.update v).L8=some B:= by
 by_cases hSel:∃e: ι,r∈F.region e
 · obtain ⟨e,he⟩:=hSel
   let A:=F.Na e
   have hOutcome: A.task.M6 T:=(W.MO e).1
   obtain ⟨a,Q,hQ,hAR⟩:=hOutcome.region.cover r he V hV
   change A.task.embed.toFun a=r at hAR
   subst r
   have hMap: Q.Nd A.task.embed=V:=
     Option.some.inj ((hOutcome.region.frame.present a Q hQ).symm.trans hV)
   let B: tF:=⟨A.task.NI.history,
     A.task.NI.history.oF hi (F.Lu e),
     A.closed,a,Q,A.NA.NY.result.complete a Q hQ⟩
   refine ⟨B,?_⟩
   intro v hv
   have hPre: v∈Q.tree.vertices.image A.task.embed.toFun:=by
     rw [←Q.Aj A.task.embed,hMap]
     exact hv
   obtain ⟨b,hb,hBV⟩:=mem_image.mp hPre
   have hAlive: b∉A.NA.NY.result.Nm:=A.NA.NY.result.k7 a Q hQ b hb
   have hOldAlive: b∉A.NA.state.Nm:=fun hh=>hAlive (A.NA.NY.In hh)
   have hRegion: v∈F.region e:=by
     have hh:=hOutcome.L1 b hOldAlive
     change A.task.embed.toFun b∈F.region e at hh
     rwa [hBV] at hh
   have hPhysical: v∉T.Nm:=T.k7 _ V hV v hv
   have hOld: v∉S.Nm:=by
     obtain ⟨es,hPass⟩:=W.M9
     exact fun hh=>hPhysical (hPass.In hh)
   have hID: A.task.NI.history.identity b=ids v:=
     (A.Mz b).symm.trans (congrArg ids hBV)
   rw [F.Mj e v hRegion,←hID]
   exact (A.Hp b (data v) (h.CY v hOld)).trans
     (IO.sS _ _ A.closed A.NA.NY.result a b Q hQ hb)
 · have hOutside: r∉JZ.MZ (F.tasks):=
     fun hh=>hSel ((F.HV r).mp hh)
   have hOld: S.ND.state r=some V:=(W.support.DO r hOutside).symm.trans hV
   obtain ⟨B,hB⟩:=h.El r V hOld
   refine ⟨B,?_⟩
   intro v hv
   have hNone:∀e: ι,v∉F.region e:=by
     intro e he
     apply hSel
     refine ⟨e,?_⟩
     exact (F.NQ e r V hOld v hv).mp he
   rw [F.E4 v hNone]
   exact hB v hv
end Be.wE
end
noncomputable section
namespace Be.wE
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)} {S T: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   {mode external: Bool} {ι: Type} [Fintype ι]
   (F: wE S ids hi out hOut data mode external ι)
   (h: Fi S ids hi out hOut data) (W: F.Witness T)
include W h in
lemma Dl: Fi T ids hi out hOut
   (F.update):= by
 refine ⟨?_,?_,F.Hh h W,F.Fx h W,
   F.J8 h W,F.wM h W,
   F.oG h W,F.Hi h W⟩
 · intro v
   exact (F.GX v).1.trans (h.neighbors v)
 · intro v
   exact (F.GX v).2.1.trans (h.Jf v)
end Be.wE
end
noncomputable section
namespace Be.IO
lemma MJ (D: IO) (j: ℕ) (hKey: j∈D.keys):(j,D.node j)∈D:= by
 have hExists:∃z,(j,z)∈D:=by
   obtain ⟨⟨a,z⟩,hZ,hEq⟩:=mem_image.mp hKey
   change a=j at hEq
   subst a
   exact ⟨z,hZ⟩
 unfold node lookup
 rw [dif_pos hExists]
 exact hExists.choose_spec
def Homogeneous (D: IO): Prop:=∃label,∀z∈D,z.2.leader z.1=label
namespace NR
variable {D: IO} {ell: ℕ} {S: tI D.history.graph D.history.MG ell}
   {mode: Bool} {u v: Fin D.history.keys.card}
lemma IY (W: NR S mode u v): S.NV.Adj u v:= by
 cases W with
 | augmentation R h => exact R.IY
 | extension hMode R hNo A => exact R.IY
end NR
lemma Bw (D: IO) (ell: ℕ) (mode external: Bool) (W: JR D ell mode external):
   D.history.identity W.tail∈D.keys∧ D.history.identity W.head∈D.keys:= by
 have hLive:=W.NY.IY
 have hAlive:=W.state.HK W.tail W.head hLive
 have hRemoved:=(D.Lf ell W.state W.valid).Nm
 rw [hRemoved] at hAlive
 have hTail: W.tail∈D.alive:=by simpa only [mem_sdiff,mem_univ,true_and,not_not] using hAlive.1
 have hHead: W.head∈D.alive:=by simpa only [mem_sdiff,mem_univ,true_and,not_not] using hAlive.2
 exact ⟨(mem_filter.mp hTail).2.1,(mem_filter.mp hHead).2.1⟩
lemma rE (D: IO) (ell: ℕ) (mode: Bool) (hD: D.Homogeneous):
   ¬Nonempty (JR D ell mode true):= by
 rintro ⟨W⟩
 obtain ⟨label,hLabel⟩:=hD
 have hKeys:=D.Bw ell mode true W
 have hTail:=hLabel _ (D.MJ _ hKeys.1)
 have hHead:=hLabel _ (D.MJ _ hKeys.2)
 exact W.cross rfl (hTail.trans hHead.symm)
lemma iZ (D: IO) (ell: ℕ) (mode: Bool) (hD: D.Homogeneous):
   D.Kc ell mode true=none:= by
 unfold Kc
 rw [dif_neg (D.rE ell mode hD)]
lemma d1 (D: IO) (ell: ℕ) (mode: Bool) (hD: D.Homogeneous)
   (j: ℕ) (old: Ln): D.Lt ell mode true j old=old:= by
 unfold Lt
 split_ifs<;> simp only [D.iZ ell mode hD]
end Be.IO
namespace Be.tE
variable {N size: ℕ} {G: SimpleGraph (Fin N)} (P: tE G size)
   (ids: Fin N→ ℕ) (data: Fin N→ Ln)
lemma u7 (hTags:∀v,(data v).leader (ids v)=ids (P.leader v)) (u: Fin N):
   IO.Homogeneous (P.NI ids data u):= by
 refine ⟨ids (P.leader u),?_⟩
 intro z hz
 obtain ⟨v,hV,hEq⟩:=mem_image.mp hz
 subst z
 change (data v).leader (ids v)=_
 rw [hTags v,(mem_filter.mp hV).2]
end Be.tE
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
inductive Lo: tI G M ell→ tI G M ell→ Prop where
 | erase (S: tI G M ell) (E: Finset (Sym2 (Fin N)))
     (hM:∀u v,M.Adj u v→ s(u,v)∉E)
     (hMemory:∀r R,S.ND.state r=some R→∀u v,(u,v)∈R.tree.NS→ s(u,v)∉E):
     Lo S (S.DH E hM hMemory)
lemma Lo.LG {S T: tI G M ell} (h: Lo S T): T.ND=S.ND:= by cases h;rfl
lemma Lo.LO {S T: tI G M ell} (h: Lo S T): T.labels=S.labels:= by cases h;rfl
lemma Lo.KY {S T: tI G M ell} (h: Lo S T): T.Nm=S.Nm:= by cases h;rfl
lemma Lo.MC {S T: tI G M ell} (h: Lo S T): T.found=S.found:= by cases h;rfl
lemma Lo.MF {S T: tI G M ell} (h: Lo S T): T.NV≤ S.NV:= by cases h;exact fun _ _ he=>he.1
lemma Lo.rank_eq {S T: tI G M ell} (h: Lo S T): T.LN=S.LN:= by cases h;rfl
lemma Lo.Nr {S T: tI G M ell} (h: Lo S T): T.G1=S.G1:= by cases h;rfl
lemma Lo.MH {S T: tI G M ell} (h: Lo S T)
   (hNo: S.ND.n8 S.NV): T.ND.n8 T.NV:= by
 rw [h.LG]
 intro r s hNe A B hA hB u v hLive
 exact hNo r s hNe A B hA hB u v (h.MF hLive)
lemma Lo.xA {S T: tI G M ell} (h: Lo S T)
   (hInternal: S.zA): T.zA:= by
 intro r R hR u v hLive
 rw [h.LG] at hR
 exact hInternal r R hR u v (h.MF hLive)
def Fl (mode: Bool) (es: List (Fin N ×Fin N))
   (S T: tI G M ell): Prop:=
 ∃U,M2 mode es S U∧ Lo U T
lemma Fl.MF {mode: Bool} {es: List (Fin N ×Fin N)} {S T: tI G M ell}
   (h: Fl mode es S T): T.NV≤ S.NV:= by
 obtain ⟨U,hPass,hPrune⟩:=h
 exact hPrune.MF.trans hPass.MF
lemma Fl.In {mode: Bool} {es: List (Fin N ×Fin N)} {S T: tI G M ell}
   (h: Fl mode es S T): S.Nm⊆T.Nm:= by
 obtain ⟨U,hPass,hPrune⟩:=h
 rw [hPrune.KY]
 exact hPass.In
lemma Fl.Jj {mode: Bool} {es: List (Fin N ×Fin N)} {S T: tI G M ell}
   (h: Fl mode es S T):∀e,T.labels e≤ S.labels e:= by
 obtain ⟨U,hPass,hPrune⟩:=h
 rw [hPrune.LO]
 exact hPass.Jj
lemma Fl.Ml {mode: Bool} {es: List (Fin N ×Fin N)} {S T: tI G M ell}
   (h: Fl mode es S T): T.G1≤ S.G1:= by
 obtain ⟨U,hPass,hPrune⟩:=h
 rw [hPrune.Nr]
 exact hPass.Ml
lemma Fl.qP {mode: Bool} {es: List (Fin N ×Fin N)} {S T: tI G M ell}
   (h: Fl mode es S T): T.ND.IS⊆S.ND.IS:= by
 obtain ⟨U,hPass,hPrune⟩:=h
 rw [hPrune.LG]
 exact hPass.qP
lemma Fl.tS {es: List (Fin N ×Fin N)} {S T: tI G M ell}
   (h: Fl false es S T) {r: Fin N} (R: Lp G M r) (hR: T.ND.state r=some R):
   S.ND.state r=some R:= by
 obtain ⟨U,hPass,hPrune⟩:=h
 rw [hPrune.LG] at hR
 exact hPass.tS R hR
lemma Fl.Bv {es: List (Fin N ×Fin N)} {S T: tI G M ell}
   (h: Fl false es S T): T.labels=S.labels:= by
 obtain ⟨U,hPass,hPrune⟩:=h
 exact hPrune.LO.trans hPass.Bv
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell} {x y: Fin N}
lemma Fl.CX {mode: Bool} {es: List (Fin N ×Fin N)} {T: tI G M ell}
   (h: Fl mode es S T): G8.Df S.ND T.ND:= by
 obtain ⟨U,hPass,hPrune⟩:=h
 simp only [hPrune.LG,hPrune.LO,hPrune.KY] at*
 exact hPass.CX
lemma Fl.lY {mode: Bool} {es: List (Fin N ×Fin N)} (h: Fl mode es S T):
   G8.oA S.ND T.ND:= by
 obtain ⟨U,hPass,hPrune⟩:=h
 simp only [hPrune.LG,hPrune.LO,hPrune.KY] at*
 exact hPass.lY
lemma Fl.lP {S T: tI G M ell} {mode: Bool} {es: List (Fin N ×Fin N)}
   (h: Fl mode es S T):∀e: Fin N ×Fin N,e.1∉ T.Nm→ S.ND.IP e→ T.ND.IP e:= by
 obtain ⟨U,hPass,hPrune⟩:=h
 simp only [hPrune.LG,hPrune.LO,hPrune.KY] at*
 exact hPass.lP
lemma Fl.q9 {mode: Bool} {es: List (Fin N ×Fin N)} (h: Fl mode es S T):
   ∀a b: Fin N ×Fin N,¬M.Adj a.2 b.2→ a.1∉ T.Nm→
     S.ND.JV a b→ T.ND.JV a b:= by
 obtain ⟨U,hPass,hPrune⟩:=h
 simp only [hPrune.LG,hPrune.LO,hPrune.KY] at*
 exact hPass.q9
lemma Fl.yF {mode: Bool} {es: List (Fin N ×Fin N)} (h: Fl mode es S T):
   ∀e: Fin N ×Fin N,e.1∉ T.Nm→ S.ND.M7 e→ T.ND.M7 e:= by
 obtain ⟨U,hPass,hPrune⟩:=h
 simp only [hPrune.LG,hPrune.LO,hPrune.KY] at*
 exact hPass.yF
lemma Fl.vK {mode: Bool} {es: List (Fin N ×Fin N)} (h: Fl mode es S T)
   (e: Fin N ×Fin N) (k: ℕ) (halive: e.1∉ T.Nm) (hs: S.ND.Bg e k): T.ND.Bg e k:= by
 obtain ⟨U,hPass,hPrune⟩:=h
 simp only [hPrune.LG,hPrune.LO,hPrune.KY] at*
 exact hPass.vK e k halive hs
lemma Fl.o6 {mode: Bool} {es: List (Fin N ×Fin N)} (h: Fl mode es S T):
   ∀e: Fin N ×Fin N,e.1∉ T.Nm→ T.labels e< S.labels e→ T.ND.Bg e (T.labels e-1):= by
 obtain ⟨U,hPass,hPrune⟩:=h
 simp only [hPrune.LG,hPrune.LO,hPrune.KY] at*
 exact hPass.o6
lemma Fl.Ds {mode: Bool} {es: List (Fin N ×Fin N)} (h: Fl mode es S T)
   (a: ℕ→ Fin N ×Fin N) (n k: ℕ) (hn: 0< n) (E: Finset (Fin N ×Fin N))
   (hE:∀e∈ E,∃i,i< n∧(e= a i∨ e=(a i).swap))
   (hmatched:∀i,i< n→ M.Adj (a i).1 (a i).2)
   (hUnmatched:∀i,i+1< n→¬M.Adj (a i).2 (a (i+1)).1):
   (∀i,i< n→(a i).1∉ T.Nm)→
     S.ND.G4 a n k E→ T.ND.G4 a n k E:= by
 obtain ⟨U,hPass,hPrune⟩:=h
 simp only [hPrune.LG,hPrune.LO,hPrune.KY] at*
 exact hPass.Ds a n k hn E hE hmatched hUnmatched
lemma Fl.F4 {es: List (Fin N ×Fin N)} (h: Fl false es S T)
   (hNow: S.ND.M5 S.labels): T.ND.M5 T.labels:= by
 obtain ⟨U,hPass,hPrune⟩:=h
 simp only [hPrune.LG,hPrune.LO,hPrune.KY] at*
 exact hPass.F4 hNow
lemma Fl.iL {es: List (Fin N ×Fin N)} (h: Fl false es S T)
   (hS: S.zA): T.zA:= by
 obtain ⟨U,hPass,hPrune⟩:=h
 exact hPrune.xA (hPass.iL hS)
lemma Fl.qO {mode: Bool} {es: List (Fin N ×Fin N)}
   (h: Fl mode es S T) (r: Fin N) (hAlive: r∉ T.Nm)
   (hActive: r∈ S.ND.IS): r∈ T.ND.IS:= by
 obtain ⟨U,hPass,hPrune⟩:=h
 simp only [hPrune.LG,hPrune.KY] at*
 exact hPass.qO r hAlive hActive
lemma Fl.c1 {mode: Bool} {es: List (Fin N ×Fin N)}
   (h: Fl mode es S T) {r: Fin N} (hNo: r∉S.ND.IS) (Q: Lp G M r)
   (hQ: T.ND.state r=some Q):
   ∃B,S.ND.state r=some B∧ Q.tree.vertices ⊆B.tree.vertices:= by
 obtain ⟨U,hPass,hPrune⟩:=h
 simp only [hPrune.LG,hPrune.KY] at*
 exact hPass.c1 hNo Q hQ
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma Fl.rZ {mode: Bool} {es: List (Fin N ×Fin N)}
   (h: Fl mode es S T):
   T.ND.Gc.card+2*T.LN≤ S.ND.Gc.card+2*S.LN:= by
 obtain ⟨U,hPass,hPrune⟩:=h
 rw [hPrune.LG,hPrune.rank_eq]
 exact hPass.rZ
lemma Fl.n5 {mode: Bool} {es: List (Fin N ×Fin N)}
   (h: Fl mode es S T) (hInternal: S.zA)
   {r: Fin N} (A: Lp G M r) (hA: T.ND.state r= some A) (hmod: A.modified= false)
   (P: v9 G M r) (hactive: A.active= some P)
   (i j: ℕ) (hi: i< P.length) (hj: j< P.length)
   (hedge: T.NV.Adj (P.KA i).2 (P.KA j).2)
   (hM:¬M.Adj (P.KA i).2 (P.KA j).2):
   ((P.KA i).2,(P.KA j).2)∈ A.tree.NS:= by
 obtain ⟨B,hB,hBm,hBA,hBH,hBE⟩:= h.CX r A hA hmod
 have hBactive: B.active= some P:= hBA.symm.trans hactive
 have hBi:= B.tL P hBactive i hi
 have hBj:= B.tL P hBactive j hj
 have hEdgeOld:= h.MF hedge
 have hcache:= hInternal r B hB _ _ hEdgeOld
   (B.tree.yG _ hBi).2 (B.tree.yG _ hBj).2 hM
 have hlink: S.ND.JV (P.KA i) (P.KA j):=⟨r,B,hB,hBi,hBj,hcache⟩
 have hAi:= A.tL P hactive i hi
 have halive:= T.k7 r A hA (P.KA i).1 (A.tree.yG _ hAi).1
 obtain ⟨s,C,hC,hCi,hCj,hcached⟩:= h.q9 (P.KA i) (P.KA j) hM halive hlink
 have hrs:= T.ND.EF r s (P.KA i) ⟨A,hA,hAi⟩ ⟨C,hC,hCi⟩
 subst s
 have hCA: C= A:= Option.some.inj (hC.symm.trans hA)
 subst C
 exact hcached
lemma Fl.fX {mode: Bool} {es: List (Fin N ×Fin N)}
   (h: Fl mode es S T) (hInternal: S.zA)
   {r: Fin N} (A: Lp G M r) (hA: T.ND.state r= some A) (hmod: A.modified= false)
   (u v: Fin N) (huv: T.NV.Adj u v) (hu: u∈ A.tree.vertices) (hv: v∈ A.tree.vertices) (hm:¬M.Adj u v):
   (u,v)∈ A.tree.NS:= by
 obtain ⟨B,hB,hBm,hVertices,hGraph,hCache⟩:= h.lY r A hA hmod
 exact hCache u v (hInternal r B hB u v (h.MF huv) (hVertices hu) (hVertices hv) hm) hu hv hm
lemma Fl.fW {mode: Bool} {es: List (Fin N ×Fin N)}
   (h: Fl mode es S T) (hInternal: S.zA)
   {r: Fin N} (A: Lp G M r) (hA: T.ND.state r= some A) (hmod: A.modified= false)
   (u v: Fin N) (huv: T.NV.Adj u v) (hu: u∈ A.tree.vertices) (hv: v∈ A.tree.vertices):
   (Mv G A.tree.NS).Adj u v:= by
 by_cases hm: M.Adj u v
 · exact A.tree.kW T.MG u v hm hu
 · exact ⟨T.MF huv,Or.inl (h.fX hInternal A hA hmod u v huv hu hv hm)⟩
lemma Fl.h9 {mode: Bool} {es: List (Fin N ×Fin N)}
   (h: Fl mode es S T) (hInternal: S.zA)
   {r: Fin N} (A: Lp G M r) (hA: T.ND.state r= some A) (hmod: A.modified= false)
   (P: v9 G M r) (hVertices: P.support ⊆A.tree.vertices)
   (hLive:∀i,i< 2*P.length→ T.NV.Adj (P.vertex i) (P.vertex (i+1))): P.Nv A.tree.NS:= by
 let Q:= P.Nq (Mv G A.tree.NS) (fun i hi=>
   h.fW hInternal A hA hmod _ _ (hLive i hi)
     (hVertices (P.mem_support i (by omega))) (hVertices (P.mem_support (i+1) (by omega))))
 exact T.complete r A hA Q
lemma Fl.fV {mode: Bool} (limit: ℕ) {es: List (Fin N ×Fin N)}
   (h: Fl mode es (S.IX limit) T) {r: Fin N}
   (A: Lp G M r) (hA: T.ND.state r= some A) (hmod: A.modified= false): A.extended= false:= by
 obtain ⟨B,hB,hBm,hBA,hBH,hBE⟩:= h.CX r A hA hmod
 have hBext: B.extended= false:= by
   change (S.ND.state r).map (fun R=> R.IX limit)= some B at hB
   obtain ⟨C,hC,hCB⟩:= Option.map_eq_some_iff.mp hB
   rw [←hCB]
   rfl
 exact hBE.trans hBext
lemma Fl.gC (S T: tI G M ell) (limit: ℕ)
   (es: List (Fin N ×Fin N)) (h: Fl true es (S.IX limit) T):
   T.ND.Gc.card≤ 2*(S.LN-T.LN):= by
 have hm:= h.rZ
 rw [S.dQ,card_empty,zero_add] at hm
 change T.ND.Gc.card+2*T.LN≤ 2*S.LN at hm
 omega
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
structure J3 (G: SimpleGraph (Fin N)) where
 edges: List (Fin N ×Fin N)
structure y5 (mode: Bool) (es: List (Fin N ×Fin N))
   (S T: tI G M ell): Prop where
 Np: Fl mode es S T
 KI: mode=true→∀x y (R: y7 T x y),R.state.modified=false→ False
 MH: mode=false→ T.ND.n8 T.NV
lemma y5.Ax {S T: tI G M ell} {x y: Fin N}
   (O: J3 G) (h: y5 true O.edges S T)
   (R: y7 T x y) (hm: R.state.modified=false): False:= h.KI rfl x y R hm
lemma y5.Dt {S T: tI G M ell}
   (O: J3 G) (h: y5 false O.edges S T):
   T.ND.n8 T.NV:= h.MH rfl
variable {S T: tI G M ell}
lemma y5.MF {mode: Bool} {es: List (Fin N ×Fin N)} {S T: tI G M ell}
   (h: y5 mode es S T): T.NV≤ S.NV:= by
 exact h.Np.MF
lemma y5.In {mode: Bool} {es: List (Fin N ×Fin N)} {S T: tI G M ell}
   (h: y5 mode es S T): S.Nm⊆T.Nm:= by
 exact h.Np.In
lemma y5.Jj {mode: Bool} {es: List (Fin N ×Fin N)} {S T: tI G M ell}
   (h: y5 mode es S T):∀e,T.labels e≤ S.labels e:= by
 exact h.Np.Jj
lemma y5.Ml {mode: Bool} {es: List (Fin N ×Fin N)} {S T: tI G M ell}
   (h: y5 mode es S T): T.G1≤ S.G1:= by
 exact h.Np.Ml
lemma y5.qP {mode: Bool} {es: List (Fin N ×Fin N)} {S T: tI G M ell}
   (h: y5 mode es S T): T.ND.IS⊆S.ND.IS:= by
 exact h.Np.qP
lemma y5.tS {es: List (Fin N ×Fin N)} {S T: tI G M ell}
   (h: y5 false es S T) {r: Fin N} (R: Lp G M r) (hR: T.ND.state r=some R):
   S.ND.state r=some R:= by
 exact h.Np.tS R hR
lemma y5.Bv {es: List (Fin N ×Fin N)} {S T: tI G M ell}
   (h: y5 false es S T): T.labels=S.labels:= by
 exact h.Np.Bv
lemma y5.CX {mode: Bool} {es: List (Fin N ×Fin N)} {T: tI G M ell}
   (h: y5 mode es S T): G8.Df S.ND T.ND:= by
 exact h.Np.CX
lemma y5.lY {mode: Bool} {es: List (Fin N ×Fin N)} (h: y5 mode es S T):
   G8.oA S.ND T.ND:= by
 exact h.Np.lY
lemma y5.lP {S T: tI G M ell} {mode: Bool} {es: List (Fin N ×Fin N)}
   (h: y5 mode es S T):∀e: Fin N ×Fin N,e.1∉ T.Nm→ S.ND.IP e→ T.ND.IP e:= by
 exact h.Np.lP
lemma y5.q9 {mode: Bool} {es: List (Fin N ×Fin N)} (h: y5 mode es S T):
   ∀a b: Fin N ×Fin N,¬M.Adj a.2 b.2→ a.1∉ T.Nm→
     S.ND.JV a b→ T.ND.JV a b:= by
 exact h.Np.q9
lemma y5.yF {mode: Bool} {es: List (Fin N ×Fin N)} (h: y5 mode es S T):
   ∀e: Fin N ×Fin N,e.1∉ T.Nm→ S.ND.M7 e→ T.ND.M7 e:= by
 exact h.Np.yF
lemma y5.vK {mode: Bool} {es: List (Fin N ×Fin N)} (h: y5 mode es S T)
   (e: Fin N ×Fin N) (k: ℕ) (halive: e.1∉ T.Nm) (hs: S.ND.Bg e k): T.ND.Bg e k:= by
 exact h.Np.vK e k halive hs
lemma y5.o6 {mode: Bool} {es: List (Fin N ×Fin N)} (h: y5 mode es S T):
   ∀e: Fin N ×Fin N,e.1∉ T.Nm→ T.labels e< S.labels e→ T.ND.Bg e (T.labels e-1):= by
 exact h.Np.o6
lemma y5.Ds {mode: Bool} {es: List (Fin N ×Fin N)} (h: y5 mode es S T)
   (a: ℕ→ Fin N ×Fin N) (n k: ℕ) (hn: 0< n) (E: Finset (Fin N ×Fin N))
   (hE:∀e∈ E,∃i,i< n∧(e= a i∨ e=(a i).swap))
   (hmatched:∀i,i< n→ M.Adj (a i).1 (a i).2)
   (hUnmatched:∀i,i+1< n→¬M.Adj (a i).2 (a (i+1)).1):
   (∀i,i< n→(a i).1∉ T.Nm)→
     S.ND.G4 a n k E→ T.ND.G4 a n k E:= by
 exact h.Np.Ds a n k hn E hE hmatched hUnmatched
lemma y5.F4 {es: List (Fin N ×Fin N)} (h: y5 false es S T)
   (hNow: S.ND.M5 S.labels): T.ND.M5 T.labels:= by
 exact h.Np.F4 hNow
lemma y5.iL {es: List (Fin N ×Fin N)} (h: y5 false es S T)
   (hS: S.zA): T.zA:= by
 exact h.Np.iL hS
lemma y5.gC (S T: tI G M ell) (limit: ℕ)
   (es: List (Fin N ×Fin N)) (h: y5 true es (S.IX limit) T):
   T.ND.Gc.card≤ 2*(S.LN-T.LN):= by
 exact h.Np.gC S T limit es
lemma y5.n5 {mode: Bool} {es: List (Fin N ×Fin N)}
   (h: y5 mode es S T) (hInternal: S.zA)
   {r: Fin N} (A: Lp G M r) (hA: T.ND.state r= some A) (hmod: A.modified= false)
   (P: v9 G M r) (hactive: A.active= some P)
   (i j: ℕ) (hi: i< P.length) (hj: j< P.length)
   (hedge: T.NV.Adj (P.KA i).2 (P.KA j).2)
   (hM:¬M.Adj (P.KA i).2 (P.KA j).2):
   ((P.KA i).2,(P.KA j).2)∈ A.tree.NS:= by
 exact h.Np.n5 hInternal A hA hmod P hactive i j hi hj hedge hM
lemma y5.h9 {mode: Bool} {es: List (Fin N ×Fin N)}
   (h: y5 mode es S T) (hInternal: S.zA)
   {r: Fin N} (A: Lp G M r) (hA: T.ND.state r= some A) (hmod: A.modified= false)
   (P: v9 G M r) (hVertices: P.support ⊆A.tree.vertices)
   (hLive:∀i,i< 2*P.length→ T.NV.Adj (P.vertex i) (P.vertex (i+1))): P.Nv A.tree.NS:= by
 exact h.Np.h9 hInternal A hA hmod P hVertices hLive
lemma y5.fV {mode: Bool} (limit: ℕ) {es: List (Fin N ×Fin N)}
   (h: y5 mode es (S.IX limit) T) {r: Fin N}
   (A: Lp G M r) (hA: T.ND.state r= some A) (hmod: A.modified= false): A.extended= false:= by
 exact h.Np.fV limit A hA hmod
lemma y5.qO {mode: Bool} {es: List (Fin N ×Fin N)}
   (h: y5 mode es S T) (r: Fin N) (hAlive: r∉ T.Nm)
   (hActive: r∈ S.ND.IS): r∈ T.ND.IS:= by
 exact h.Np.qO r hAlive hActive
lemma y5.c1 {mode: Bool} {es: List (Fin N ×Fin N)}
   (h: y5 mode es S T) {r: Fin N} (hNo: r∉S.ND.IS) (Q: Lp G M r)
   (hQ: T.ND.state r=some Q):
   ∃B,S.ND.state r=some B∧ Q.tree.vertices ⊆B.tree.vertices:= by
 exact h.Np.c1 hNo Q hQ
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
namespace tI
def iE (S: tI G M ell): Prop:=
 ∀x y (R: y7 S x y),S.ND.Mm R.root y→ False
def aY (S: tI G M ell): Prop:=
 ∀x y (R: y7 S x y),R.state.modified=false→ S.ND.Mm R.root y→ False
end tI
lemma M2.d7 {S T: tI G M ell} {mode: Bool}
   {es: List (Fin N ×Fin N)} (h: M2 mode es S T)
   (hClosed: S.iE): T.aY:= by
 intro x y R hMod hOwn
 obtain ⟨A,hA,hy⟩:=hOwn
 have hAR: A=R.state:=Option.some.inj (hA.symm.trans R.present)
 subst A
 obtain ⟨B,hB,hBm,hVertices,hGraph,hCache⟩:=h.lY R.root R.state R.present hMod
 obtain ⟨Q,hRoot⟩:=h.jT R hMod
 apply hClosed x y Q
 rw [hRoot]
 exact ⟨B,hB,hVertices hy⟩
lemma M2.Bt {S T: tI G M ell}
   {es: List (Fin N ×Fin N)} (h: M2 false es S T):
   y5 false es S T.vL where
 Np:=⟨T,h,Lo.erase T T.l9
   T.bA T.b6⟩
 KI:= by intro h;cases h
 MH:= fun _=>T.dB
lemma M2.qW {S T: tI G M ell}
   {es: List (Fin N ×Fin N)} (h: M2 true es S T)
   (hClosed: S.iE): y5 true es S T.Cs where
 Np:=⟨T,h,Lo.erase T T.tZ
   T.cB T.e1⟩
 KI:= fun _ x y R hMod=>T.eF (h.d7 hClosed) x y R hMod
 MH:= by intro h;cases h
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
namespace tI
def zE (S: tI G M ell): Prop:=
 ∀r R,S.ND.state r=some R→ R.modified=true→ R.extended=true
def tG (S: tI G M ell) (r: Fin N): Prop:=
 ∀x y (R: y7 S x y),R.root=r→ S.ND.Mm R.root y→ False
lemma iI (S: tI G M ell) (L: ℕ):(S.IX L).zE:= by
 intro r R hR hMod
 change (S.ND.state r).map (fun A=>A.IX L)=some R at hR
 obtain ⟨A,hA,hAR⟩:=Option.map_eq_some_iff.mp hR
 rw [←hAR] at hMod
 change false=true at hMod
 cases hMod
end tI
namespace y7
variable {S: tI G M ell} {x y: Fin N} (R: y7 S x y)
lemma gJ (hOwn: S.ND.Mm R.root y):¬S.Bd x y true:= by
 rintro ⟨A,hFlag⟩
 have hLeft:=S.ND.BE A.ME R.root x
   ⟨A.left,A.HJ,A.M1⟩ ⟨R.state,R.present,R.K5⟩
 have hRight:=S.ND.BE A.L7 R.root y
   ⟨A.right,A.GE,A.head_mem⟩ hOwn
 exact A.distinct (hLeft.trans hRight.symm)
def DZ (hOwn: S.ND.Mm R.root y): Bb R:=
 Bb.single (Or.inr ((S.ND.KP R.root y).mpr hOwn))
lemma m1 (hOwn: S.ND.Mm R.root y):
   (R.DZ hOwn).Nj.tG R.root:= by
 obtain ⟨B,hB,hActive,hMod,hExt,hHeld⟩:=(R.DZ hOwn).EG
 intro a b Q hRoot hOwnQ
 have hExtended:∀s (A: Lp G M s),(R.DZ hOwn).Nj.ND.state s=some A→
     s=R.root→ A.extended=true:= by
   intro s A hA hSame
   subst s
   have hAB: A=B:=Option.some.inj (hA.symm.trans hB)
   rw [hAB]
   exact hExt
 have hQExt:=hExtended Q.root Q.state Q.present hRoot
 rw [Q.H9] at hQExt
 cases hQExt
lemma a8 (hOwn: S.ND.Mm R.root y) (hFlags: S.zE):
   (R.DZ hOwn).Nj.zE:= by
 obtain ⟨B,hB,hActive,hMod,hExt,hHeld⟩:=(R.DZ hOwn).EG
 intro s Q hQ hQMod
 by_cases hSame: s=R.root
 · subst s
   have hQB: Q=B:=Option.some.inj (hQ.symm.trans hB)
   rw [hQB]
   exact hExt
 · have hOld: S.ND.state s=some Q:= by
     change Function.update S.ND.state R.root _ s=some Q at hQ
     rw [Function.update_of_ne hSame] at hQ
     exact hQ
   exact hFlags s Q hOld hQMod
end y7
inductive zC (r: Fin N): tI G M ell→ tI G M ell→ Prop where
 | idle {S: tI G M ell} (hClosed: S.tG r): zC r S S
 | update {S: tI G M ell} {x y: Fin N} (R: y7 S x y)
     (hRoot: R.root=r) (hOwn: S.ND.Mm R.root y):
     zC r S (R.DZ hOwn).Nj
lemma zC.FO (r: Fin N) (S: tI G M ell):
   ∃T,zC r S T:= by
 by_cases hClosed: S.tG r
 · exact ⟨S,zC.idle hClosed⟩
 · have hSome:∃(x y: Fin N) (R: y7 S x y),R.root=r∧ S.ND.Mm R.root y:= by
     by_contra hNot
     apply hClosed
     intro x y R hRoot hOwn
     exact hNot ⟨x,y,R,hRoot,hOwn⟩
   obtain ⟨x,y,R,hRoot,hOwn⟩:=hSome
   exact ⟨(R.DZ hOwn).Nj,zC.update R hRoot hOwn⟩
lemma zC.closed {r: Fin N} {S T: tI G M ell}
   (h: zC r S T): T.tG r:= by
 cases h with
 | idle hClosed => exact hClosed
 | update R hRoot hOwn => rw [←hRoot];exact R.m1 hOwn
lemma zC.flags {r: Fin N} {S T: tI G M ell}
   (h: zC r S T) (hFlags: S.zE): T.zE:= by
 cases h with
 | idle hClosed => exact hFlags
 | update R hRoot hOwn => exact R.a8 hOwn hFlags
lemma zC.KU {r: Fin N} {S T: tI G M ell}
   (h: zC r S T):∃es,Dc true es S T:= by
 cases h with
 | idle hClosed => exact ⟨[],Dc.nil _⟩
 | update R hRoot hOwn =>
   exact ⟨[(_,_)],Dc.cons
     (Dd.extension rfl R (R.gJ hOwn) (R.DZ hOwn)) (Dc.nil _)⟩
lemma M2.o4 {S T: tI G M ell} {mode: Bool}
   {es: List (Fin N ×Fin N)} (h: M2 mode es S T) (hFlags: T.zE)
   {r: Fin N} (hClosed: S.tG r): T.tG r:= by
 intro x y R hRoot hOwn
 have hMod: R.state.modified=false:= by
   cases hState: R.state.modified with
   | false => rfl
   | true =>
     have hExt:=hFlags R.root R.state R.present hState
     rw [R.H9] at hExt
     cases hExt
 obtain ⟨A,hA,hy⟩:=hOwn
 have hAR: A=R.state:=Option.some.inj (hA.symm.trans R.present)
 subst A
 obtain ⟨B,hB,hBm,hVertices,hGraph,hCache⟩:=h.lY R.root R.state R.present hMod
 obtain ⟨Q,hQRoot⟩:=h.jT R hMod
 exact hClosed x y Q (hQRoot.trans hRoot) (by rw [hQRoot];exact ⟨B,hB,hVertices hy⟩)
lemma Dc.append {S U T: tI G M ell} {mode: Bool}
   {es fs: List (Fin N ×Fin N)} (h: Dc mode es S U) (hRest: Dc mode fs U T):
   Dc mode (es++fs) S T:= by
 induction h with
 | nil => exact hRest
 | cons step rest ih => exact Dc.cons step (ih hRest)
inductive zB: List (Fin N)→ tI G M ell→ tI G M ell→ Prop where
 | nil (S: tI G M ell): zB [] S S
 | cons {r: Fin N} {rs: List (Fin N)} {S U T: tI G M ell}
     (step: zC r S U) (rest: zB rs U T): zB (r::rs) S T
lemma zB.FO (rs: List (Fin N)) (S: tI G M ell):
   ∃T,zB rs S T:= by
 induction rs generalizing S with
 | nil => exact ⟨S,zB.nil S⟩
 | cons r rs ih =>
   obtain ⟨U,hU⟩:=zC.FO r S
   obtain ⟨T,hT⟩:=ih U
   exact ⟨T,zB.cons hU hT⟩
lemma zB.flags {rs: List (Fin N)} {S T: tI G M ell}
   (h: zB rs S T) (hFlags: S.zE): T.zE:= by
 induction h with
 | nil => exact hFlags
 | cons step rest ih => exact ih (step.flags hFlags)
lemma zB.KU {rs: List (Fin N)} {S T: tI G M ell}
   (h: zB rs S T):∃es,Dc true es S T:= by
 induction h with
 | nil => exact ⟨[],Dc.nil _⟩
 | cons step rest ih =>
   obtain ⟨es,hES⟩:=step.KU
   obtain ⟨fs,hFS⟩:=ih
   exact ⟨es++fs,hES.append hFS⟩
lemma zB.closed {rs: List (Fin N)} {S T: tI G M ell}
   (h: zB rs S T) (hFlags: S.zE):∀r∈rs,T.tG r:= by
 induction h with
 | nil => intro r hr;simp at hr
 | @cons r rs S U T step rest ih =>
   have hFlagsU:=step.flags hFlags
   have hFlagsT:=rest.flags hFlagsU
   obtain ⟨es,hES⟩:=rest.KU
   have hR:=hES.Mh.o4 hFlagsT step.closed
   intro s hs
   rcases List.mem_cons.mp hs with hEq|hMem
   · rw [hEq];exact hR
   · exact ih hFlagsU s hMem
lemma m6 (S: tI G M ell) (hFlags: S.zE):
   ∃T es,Dc true es S T∧ T.iE∧ T.zE:= by
 obtain ⟨T,hPass⟩:=zB.FO (univ: Finset (Fin N)).toList S
 obtain ⟨es,hES⟩:=hPass.KU
 refine ⟨T,es,hES,?_,hPass.flags hFlags⟩
 intro x y R hOwn
 exact hPass.closed hFlags R.root (by simp) x y R rfl hOwn
lemma fE (S: tI G M ell) (L: ℕ):
   ∃T es,Dc true es (S.IX L) T∧ T.iE∧ T.zE:=
 m6 (S.IX L) (S.iI L)
end Be
end
noncomputable section
namespace Be
namespace tE
variable {N size: ℕ} {G: SimpleGraph (Fin N)} (P: tE G size)
def block (r: Fin N): Finset (Fin N):=univ.filter (fun v=>P.leader v=P.leader r)
def Fc (ids: Fin N→ ℕ) (data: Fin N→ Ln) (ell: ℕ):=
 {r: Fin N// P.leader r=r∧ Nonempty (IO.JR (P.NI ids data r) ell true false)}
instance (ids: Fin N→ ℕ) (data: Fin N→ Ln) (ell: ℕ):
   Fintype (P.Fc ids data ell):= by
 unfold Fc
 infer_instance
end tE
namespace Fi
variable {N ell size: ℕ} {G M: SimpleGraph (Fin N)} {S: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (h: Fi S ids hi out hOut data)
   (hSize:∀r V,S.ND.state r=some V→ V.tree.vertices.card≤ size) (hS: 2≤ size)
include h in
lemma o2
   (r:(S.tT ids hi hSize hS).Fc ids data ell):
   let P:=S.tT ids hi hSize hS
   Nonempty (qI (P.NI ids data r.val) (P.block r.val) S true ids hi out hOut
     (IO.w7 _ h (IO.u2 (P.block r.val) ids data)) false):= by
 dsimp only
 let P:=S.tT ids hi hSize hS
 let D: IO:=P.NI ids data r.val
 have hAuth:∀z∈D,∃v,z=(ids v,data v):=IO.u2 (P.block r.val) ids data
 obtain ⟨hClosed,U,hU,hEmbed⟩:=D.ER S ids hi hSize hS
   (IO.AF P ids hi data r.val) out hOut data h hAuth
 obtain ⟨W,hW⟩:=D.wO ell true false r.property.2
 have hUW: U=W.state:=Option.some.inj (hU.symm.trans W.valid)
 subst U
 have hRegion:=D.JP h hAuth hClosed W.state W.valid hEmbed
 have hSupport: D.Ig ids=P.block r.val:=
   IO.nF (P.block r.val) ids hi data
 rw [hSupport] at hRegion
 exact ⟨⟨hClosed,W,hW,hRegion⟩⟩
def HD (r:(S.tT ids hi hSize hS).Fc ids data ell):=
 Classical.choice (h.o2 hSize hS r)
def D4: wE S ids hi out hOut data true false
   ((S.tT ids hi hSize hS).Fc ids data ell) where
 NI r:=(S.tT ids hi hSize hS).NI ids data r.val
 region r:=(S.tT ids hi hSize hS).block r.val
 Lu r:=IO.w7 _ h (IO.u2
   ((S.tT ids hi hSize hS).block r.val) ids data)
 Na r:=h.HD hSize hS r
 disjoint i j hNe:=by
   apply disjoint_left.mpr
   intro v hVI hVJ
   have hI:(S.tT ids hi hSize hS).leader v=i.val:=
     (mem_filter.mp hVI).2.trans i.property.1
   have hJ:(S.tT ids hi hSize hS).leader v=j.val:=
     (mem_filter.mp hVJ).2.trans j.property.1
   exact hNe (Subtype.ext (hI.symm.trans hJ))
 NQ i r V hV v hv:=by
   change (v∈univ.filter (fun w=>(S.tT ids hi hSize hS).leader w=
     (S.tT ids hi hSize hS).leader i.val))↔ _
   simp only [tE.block,mem_filter,mem_univ,true_and]
   rw [S.iR ids hi hSize hS r V hV v hv,
     S.iR ids hi hSize hS r V hV r V.tree.MU]
end Fi
end Be
end
noncomputable section
namespace Be.Fi
variable {N ell size: ℕ} {G M: SimpleGraph (Fin N)} {S: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (h: Fi S ids hi out hOut data)
   (hSize:∀r V,S.ND.state r=some V→ V.tree.vertices.card≤ size) (hS: 2≤ size)
include h in
lemma mG (mode: Bool) (u v: Fin N):
   IO.omission
     ((S.tT ids hi hSize hS).NI ids data u∪
       (S.tT ids hi hSize hS).NI ids data v) ell mode (ids u) (ids v)↔
     s(u,v)∈(if mode then S.tZ else S.l9):= by
 let P:=S.tT ids hi hSize hS
 let D: IO:=P.NI ids data u∪P.NI ids data v
 have hAuth:∀z∈D,∃w,z=(ids w,data w):=by
   intro z hz
   rcases mem_union.mp hz with hz|hz
   · exact IO.u2 (P.block u) ids data z hz
   · exact IO.u2 (P.block v) ids data z hz
 have hSat: D.Saturated P ids:=IO.CK _ _ P ids
   (IO.AF P ids hi data u) (IO.AF P ids hi data v)
 have hU: ids u∈D.keys:=by
   rw [IO.keys,image_union]
   exact mem_union_left _ ((P.Ex ids hi data u u).mpr rfl)
 have hV: ids v∈D.keys:=by
   rw [IO.keys,image_union]
   exact mem_union_right _ ((P.Ex ids hi data v v).mpr rfl)
 exact (D.Ia S ids hi hSize hS out hOut data h hAuth hSat mode u v hU hV).trans
   (S.pT ids hi hSize hS mode u v)
include h in
lemma fH (mode: Bool) (v: Fin N):
   AC ell mode (ids v)
     (ids ((S.tT ids hi hSize hS).leader v),
       (S.tT ids hi hSize hS).NI ids data v)
     ((G.neighborFinset v).val.map (fun w=>(ids w,
       ids ((S.tT ids hi hSize hS).leader w),
       (S.tT ids hi hSize hS).NI ids data w)))=
     Hz G ids (if mode then S.tZ else S.l9) v:= by
 ext j
 constructor
 · intro hj
   obtain ⟨z,hz,hJ⟩:=mem_image.mp hj
   obtain ⟨hMessage,hOmit⟩:=mem_filter.mp hz
   obtain ⟨w,hW,hZ⟩:=Multiset.mem_map.mp (Multiset.mem_toFinset.mp hMessage)
   subst z
   apply mem_image.mpr
   exact ⟨w,mem_filter.mpr ⟨hW,(h.mG hSize hS mode v w).mp hOmit⟩,hJ⟩
 · intro hj
   obtain ⟨w,hW,hJ⟩:=mem_image.mp hj
   refine mem_image.mpr ⟨(ids w,ids ((S.tT ids hi hSize hS).leader w),
     (S.tT ids hi hSize hS).NI ids data w),mem_filter.mpr ⟨?_,?_⟩,hJ⟩
   · exact Multiset.mem_toFinset.mpr (Multiset.mem_map.mpr ⟨w,(mem_filter.mp hW).1,rfl⟩)
   · exact (h.mG hSize hS mode v w).mpr (mem_filter.mp hW).2
include h hSize hS in
lemma pO (mode: Bool): execute (yE size ell mode) G () ids data=
   FK G ids data (if mode then S.tZ else S.l9):= by
 funext v
 unfold execute yE
 rw [C7.A4,Ff.CM]
 have hInput:(fun w=>((data w).leader (ids w),data w))=
     (fun w=>(ids ((S.tT ids hi hSize hS).leader w),data w)):=by
   funext w
   exact congrArg (fun j=>(j,data w)) (h.Gr hSize hS w)
 rw [hInput]
 have hPacket:(fun w=>(Gq size).program.output G () ids
     (fun z=>(ids ((S.tT ids hi hSize hS).leader z),data z)) (fun _ _=>false) w)=
     (fun w=>(ids ((S.tT ids hi hSize hS).leader w),
       (S.tT ids hi hSize hS).NI ids data w)):=by
   funext w
   exact (S.tT ids hi hSize hS).nH ids hi data w
 have hNext: Ff.L0 (Gq size) (fun _ _ _ z=>z) G () ids
     (fun w=>(ids ((S.tT ids hi hSize hS).leader w),data w))=
     (fun w=>(ids ((S.tT ids hi hSize hS).leader w),
       (S.tT ids hi hSize hS).NI ids data w)):=hPacket
 rw [hNext,Fd.Cn]
 rw [h.fH hSize hS mode v]
 rfl
include h hSize hS in
lemma nN (mode: Bool):
   Fi (if mode then S.Cs else S.vL) ids hi out hOut
     (execute (yE size ell mode) G () ids data):= by
 rw [h.pO hSize hS mode]
 cases mode
 · exact h.DI S.l9 S.bA S.b6
 · exact h.DI S.tZ S.cB S.e1
end Be.Fi
end
noncomputable section
namespace Be
structure zF {N ell: ℕ} {G M: SimpleGraph (Fin N)}
   (D: IO) (X: Finset (Fin N)) (S: tI G M ell) (mode: Bool)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (out: Fin N→ Option ℕ)
   (hOut: ReportsMatching G ids out M) (hAuth: D.history.Li G ids out) where
 closed: D.history.JX
 NA: IO.JR D ell mode true
 Lz: D.Kc ell mode true=some NA
 region: Bh (D.history.embedding hAuth hi hOut closed) NA.state X S
namespace zF
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)} {D: IO} {X: Finset (Fin N)}
   {S: tI G M ell} {mode: Bool} {ids: Fin N→ ℕ} {hi: Function.Injective ids}
   {out: Fin N→ Option ℕ} {hOut: ReportsMatching G ids out M} {hAuth: D.history.Li G ids out}
   (A: zF D X S mode ids hi out hOut hAuth)
def task: JZ G M ell mode:=
 ⟨D,A.NA.state,D.history.embedding hAuth hi hOut A.closed,X,A.NA.tail,A.NA.head,A.NA.NY⟩
lemma Lw: A.task.Lj S:=A.region
end zF
namespace Fi
variable {N ell size: ℕ} {G M: SimpleGraph (Fin N)} {S: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (h: Fi S ids hi out hOut data)
   (hSize:∀r A,S.ND.state r=some A→ A.tree.vertices.card≤ size) (hS: 2≤ size)
   (mode: Bool) (R: SimpleGraph (Fin N))
variable (hR: Matching ((S.tT ids hi hSize hS).Lv (tE.Lx (S.tT ids hi hSize hS) ids data (IO.Fz ell mode)) (tE.Dr (S.tT ids hi hSize hS) ids data (IO.Fz ell mode))) R)
include h hR in
lemma p1 (e: R.edgeSet):
   let D: IO:=(S.tT ids hi hSize hS).ES ids data e.val
   let X:=(S.tT ids hi hSize hS).ET e.val
   Nonempty (zF D X S mode ids hi out hOut
     (D.w7 h (IO.u2 X ids data))):= by
 dsimp only
 let D: IO:=(S.tT ids hi hSize hS).ES ids data e.val
 let X:=(S.tT ids hi hSize hS).ET e.val
 have hEnds:=(S.tT ids hi hSize hS).vY (tE.Lx (S.tT ids hi hSize hS) ids data (IO.Fz ell mode)) (tE.Dr (S.tT ids hi hSize hS) ids data (IO.Fz ell mode)) R hR e
 obtain ⟨ha,hb,hNe,x,y,hXA,hYB,hGraph,hCand⟩:=hR.1 hEnds.2.2
 have hDxy: D=(S.tT ids hi hSize hS).NI ids data x∪(S.tT ids hi hSize hS).NI ids data y:=by
   change (S.tT ids hi hSize hS).ES ids data e.val=_
   rw [(S.tT ids hi hSize hS).nU ids data e.val hEnds.1 hEnds.2.1]
   rw [(S.tT ids hi hSize hS).L3 ids data x (Mw e.val).1 (hXA.trans hEnds.1.symm),
     (S.tT ids hi hSize hS).L3 ids data y (Mw e.val).2 (hYB.trans hEnds.2.1.symm)]
 have hDyx: D=(S.tT ids hi hSize hS).NI ids data y∪(S.tT ids hi hSize hS).NI ids data x:=hDxy.trans (union_comm _ _)
 have hChosen: Nonempty (IO.JR D ell mode true):=by
   change IO.Mx ((S.tT ids hi hSize hS).NI ids data x∪(S.tT ids hi hSize hS).NI ids data y) ell mode (ids x) (ids y)∨
     IO.Mx ((S.tT ids hi hSize hS).NI ids data y∪(S.tT ids hi hSize hS).NI ids data x) ell mode (ids y) (ids x) at hCand
   rcases hCand with hCand|hCand
   · rw [←hDxy] at hCand
     exact D.BG ell mode (ids x) (ids y) hCand
   · rw [←hDyx] at hCand
     exact D.BG ell mode (ids y) (ids x) hCand
 have hAuthentic:∀z∈D,∃v,z=(ids v,data v):=IO.u2 X ids data
 have hSat: D.Saturated (S.tT ids hi hSize hS) ids:=(S.tT ids hi hSize hS).g8 ids hi data e.val
 obtain ⟨hClosed,U,hU,hEmbed⟩:=D.ER S ids hi hSize hS hSat out hOut data h hAuthentic
 obtain ⟨W,hW⟩:=D.wO ell mode true hChosen
 have hUW: U=W.state:=Option.some.inj (hU.symm.trans W.valid)
 subst U
 have hRegion:=D.JP h hAuthentic hClosed W.state W.valid hEmbed
 have hSupport: D.Ig ids=X:=(S.tT ids hi hSize hS).dD ids hi data e.val
 rw [hSupport] at hRegion
 exact ⟨⟨hClosed,W,hW,hRegion⟩⟩
def Iw (e: R.edgeSet):
   let D: IO:=(S.tT ids hi hSize hS).ES ids data e.val
   let X:=(S.tT ids hi hSize hS).ET e.val
   zF D X S mode ids hi out hOut
     (D.w7 h (IO.u2 X ids data)):=
 Classical.choice (h.p1 hSize hS mode R hR e)
def Ix (e: R.edgeSet): JZ G M ell mode:=
 (h.Iw hSize hS mode R hR e).task
lemma lN (e: R.edgeSet):(h.Ix hSize hS mode R hR e).Lj S:=
 (h.Iw hSize hS mode R hR e).Lw
lemma nX:
   ∃(T: tI G M ell) (es: List (Fin N ×Fin N)),
     es.length=matchingSize R∧ Dc mode es S T∧
     Bl S T (JZ.MZ ((univ: Finset R.edgeSet).toList.map (h.Ix hSize hS mode R hR)))∧
     ∀e: R.edgeSet,(h.Ix hSize hS mode R hR e).M6 T∧
       (h.Ix hSize hS mode R hR e).Bc S.labels T:= by
 let edges: List R.edgeSet:=(univ: Finset R.edgeSet).toList
 let tasks:=edges.map (h.Ix hSize hS mode R hR)
 have hEdges: edges.Pairwise (fun e f=>e≠f):=Finset.nodup_toList _
 have hTasks: tasks.Pairwise (fun A B=>Disjoint A.support B.support):=by
   apply List.pairwise_map.mpr
   apply hEdges.imp
   intro e f hNe
   exact (S.tT ids hi hSize hS).jL R _ hR e f hNe
 have hAvailable:∀A∈tasks,A.Lj S:=by
   intro A hA
   obtain ⟨e,he,hEq⟩:=List.mem_map.mp hA
   subst A
   exact h.lN hSize hS mode R hR e
 obtain ⟨T,hPass,hSupport,hOutcomes⟩:=JZ.f6 tasks hTasks S hAvailable
 refine ⟨T,tasks.map JZ.LD,?_,hPass,hSupport,?_⟩
 · simp only [tasks,edges,List.length_map,Finset.length_toList]
   exact R.edgeSet_univ_card
 · intro e
   exact hOutcomes _ (List.mem_map.mpr ⟨e,Finset.mem_toList.mpr (mem_univ _),rfl⟩)
end Fi
end Be
end
noncomputable section
namespace Be.tE
variable {N size: ℕ} {G: SimpleGraph (Fin N)} (P: tE G size)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (data: Fin N→ Ln)
   (hTags:∀v,(data v).leader (ids v)=ids (P.leader v))
   {K: Type} (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K) (ell: ℕ) (mode: Bool)
   (R: SimpleGraph (Fin N))
variable (hR: ReportsMatching (P.Lv (P.Lx ids data (IO.Fz ell mode)) (P.Dr ids data (IO.Fz ell mode))) ids
   (execute A (P.Lv (P.Lx ids data (IO.Fz ell mode)) (P.Dr ids data (IO.Fz ell mode))) k ids
     (neighborIDs (P.Lv (P.Lx ids data (IO.Fz ell mode)) (P.Dr ids data (IO.Fz ell mode))) ids)) R)
include hi hTags hR in
lemma gS (v: Fin N):
   execute (x6 A k size ell mode) G () ids data v=
     IO.Lt
       ((univ.filter (fun w=>P.HY R ids hi w=P.HY R ids hi v)).image
         (fun w=>(ids w,data w))) ell mode true (ids v) (data v):= by
 unfold execute x6
 rw [C7.A4]
 change IO.Lt (execute (KS A k size (IO.Fz ell mode)) G () ids
   (fun w=>((data w).leader (ids w),data w)) v) ell mode true (ids v) (data v)=_
 have hInput:(fun w=>((data w).leader (ids w),data w))=(fun w=>(ids (P.leader w),data w)):=by
   funext w
   exact congrArg (fun j=>(j,data w)) (hTags w)
 rw [hInput,P.u9 ids hi data A k (IO.Fz ell mode) R hR v]
include hi hTags hR in
lemma eC (e: R.edgeSet) (v: Fin N) (hv: v∈P.ET e.val):
   execute (x6 A k size ell mode) G () ids data v=
     IO.Lt (P.ES ids data e.val) ell mode true (ids v) (data v):= by
 rw [P.gS ids hi data hTags A k ell mode R hR v,
   P.k2 (P.Lx ids data (IO.Fz ell mode)) (P.Dr ids data (IO.Fz ell mode)) R hR.1 ids hi data e v hv]
end Be.tE
end
noncomputable section
namespace Be.tE
variable {N size: ℕ} {G: SimpleGraph (Fin N)} (P: tE G size)
   (Lx: Fin N→ Fin N→ Prop) (hC: Symmetric Lx)
   (R: SimpleGraph (Fin N)) (hR: Matching (P.Lv Lx hC) R)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids)
include hR
lemma uV (v: Fin N) (hFix: Ni ids hi R (P.leader v)=P.leader v):
   (univ.filter (fun w=>P.HY R ids hi w=P.HY R ids hi v))=
     (univ.filter (fun w=>P.leader w=P.leader v)):= by
 have hInv:=vA ids hi R (qJ.gP _ R hR)
 ext w
 simp only [mem_filter,mem_univ,true_and]
 change representative ids (Ni ids hi R) (P.leader w)=representative ids (Ni ids hi R) (P.leader v)↔ _
 rw [eq_comm,yI ids hi _ hInv,hFix,or_self]
lemma yP (v: Fin N):
   (∃e: R.edgeSet,v∈P.ET e.val)∨ Ni ids hi R (P.leader v)=P.leader v:= by
 rcases x7 ids hi R (P.leader v) with hFix|hEdge
 · exact Or.inr hFix
 · let e: R.edgeSet:=⟨s(P.leader v,Ni ids hi R (P.leader v)),R.mem_edgeSet.mpr hEdge⟩
   exact Or.inl ⟨e,(P.vX e.val v).mpr (by simp [e])⟩
end Be.tE
namespace Be
variable {N size: ℕ} {G: SimpleGraph (Fin N)} (P: tE G size)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (data: Fin N→ Ln)
def yO (R: SimpleGraph (Fin N)) (ell: ℕ) (mode: Bool) (v: Fin N): Ln:=
 if h:∃e: R.edgeSet,v∈P.ET e.val then
   IO.Lt (P.ES ids data h.choose.val) ell mode true (ids v) (data v)
 else data v
variable (hTags:∀v,(data v).leader (ids v)=ids (P.leader v))
   {K: Type} (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K) (ell: ℕ) (mode: Bool)
   (R: SimpleGraph (Fin N))
   (hR: ReportsMatching (P.Lv (P.Lx ids data (IO.Fz ell mode))
     (P.Dr ids data (IO.Fz ell mode))) ids
     (execute A (P.Lv (P.Lx ids data (IO.Fz ell mode))
       (P.Dr ids data (IO.Fz ell mode))) k ids
       (neighborIDs (P.Lv (P.Lx ids data (IO.Fz ell mode))
         (P.Dr ids data (IO.Fz ell mode))) ids)) R)
include hi hTags hR in
lemma sD (v: Fin N) (hFix: Ni ids hi R (P.leader v)=P.leader v):
   execute (x6 A k size ell mode) G () ids data v=data v:= by
 rw [P.gS ids hi data hTags A k ell mode R hR v,
   P.uV (P.Lx ids data (IO.Fz ell mode))
     (P.Dr ids data (IO.Fz ell mode)) R hR.1 ids hi v hFix]
 exact IO.d1 (P.NI ids data v) ell mode
   (P.u7 ids data hTags v) (ids v) (data v)
include hi hTags hR in
lemma gU: execute (x6 A k size ell mode) G () ids data=
   yO P ids data R ell mode:= by
 funext v
 unfold yO
 split_ifs with h
 · exact P.eC ids hi data hTags A k ell mode R hR h.choose v h.choose_spec
 · have hFix: Ni ids hi R (P.leader v)=P.leader v:=
     (P.yP (P.Lx ids data (IO.Fz ell mode))
       (P.Dr ids data (IO.Fz ell mode)) R hR.1 ids hi v).resolve_left h
   exact sD P ids hi data hTags A k ell mode R hR v hFix
end Be
end
noncomputable section
namespace Be.tE
variable {N size: ℕ} {G H R: SimpleGraph (Fin N)} (P: tE G size)
lemma nW (hR: Matching H R) (e f: R.edgeSet) (v: Fin N)
   (hE: v∈P.ET e.val) (hF: v∈P.ET f.val): e=f:= by
 by_contra hNe
 exact disjoint_left.mp (P.jL R H hR e f hNe) hE hF
end Be.tE
namespace Be
variable {N size: ℕ} {G H R: SimpleGraph (Fin N)} (P: tE G size)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (data: Fin N→ Ln) (ell: ℕ) (mode: Bool)
lemma p0 (hR: Matching H R) (e: R.edgeSet) (v: Fin N) (hV: v∈P.ET e.val):
   yO P ids data R ell mode v=
     IO.Lt (P.ES ids data e.val) ell mode true (ids v) (data v):= by
 unfold yO
 have hExists:∃f: R.edgeSet,v∈P.ET f.val:=⟨e,hV⟩
 rw [dif_pos hExists]
 have hEq: hExists.choose=e:=P.nW hR hExists.choose e v hExists.choose_spec hV
 rw [hEq]
lemma fM (v: Fin N) (hV:∀e: R.edgeSet,v∉P.ET e.val):
   yO P ids data R ell mode v=data v:= by
 unfold yO
 rw [dif_neg (by simpa only [not_exists] using hV)]
lemma g7 (v: Fin N):
   (yO P ids data R ell mode v).neighbors=(data v).neighbors∧
   (yO P ids data R ell mode v).Jf=(data v).Jf∧
   (yO P ids data R ell mode v).ignored=(data v).ignored:= by
 unfold yO
 split_ifs with hExists
 · exact IO.zM _ ell mode true (ids v) (data v)
 · exact ⟨rfl,rfl,rfl⟩
lemma b3 (v: Fin N) (hV:(data v).Nm=true):
   yO P ids data R ell mode v=data v:= by
 unfold yO
 split_ifs with hExists
 · exact IO.l7 _ ell mode true (ids v) (data v) hV
 · rfl
end Be
end
noncomputable section
namespace Be.zF
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)} {D: IO} {X: Finset (Fin N)}
   {S: tI G M ell} {mode: Bool} {ids: Fin N→ ℕ} {hi: Function.Injective ids}
   {out: Fin N→ Option ℕ} {hOut: ReportsMatching G ids out M} {hAuth: D.history.Li G ids out}
   (A: zF D X S mode ids hi out hOut hAuth)
lemma Mz (a: Fin D.history.keys.card): ids (A.task.embed.toFun a)=D.history.identity a:=
 D.history.yA hAuth a
lemma decode (a: Fin D.history.keys.card) (old: Ln):
   D.Lt ell mode true (D.history.identity a) old=
     D.JO (D.history.oF hi hAuth) A.closed A.NA.NY.result a old:=
 D.zL (D.history.oF hi hAuth) A.closed A.NA A.Lz a old
lemma FF (base: Fin N ×Fin N→ ℕ) (a: Fin D.history.keys.card) (old: Ln)
   (hOld: old.Nm=false) (hBase:∀w,old.labels (ids w)=base (A.task.embed.toFun a,w)) (w: Fin N):
   (D.Lt ell mode true (D.history.identity a) old).labels (ids w)=A.task.HG base a w:= by
 rw [A.decode]
 exact D.eO (D.history.oF hi hAuth) A.closed
   A.NA.NY.result A.task.embed ids hi A.Mz base a old hOld hBase w
lemma Dx (a: Fin D.history.keys.card) (old: Ln) (hOld: old.Nm=false):
   (D.Lt ell mode true (D.history.identity a) old).Nm=true↔ a∈A.NA.NY.result.Nm:= by
 rw [A.decode]
 exact D.s6 _ _ _ a old hOld
lemma Hp (a: Fin D.history.keys.card) (old: Ln) (hOld: old.Nm=false):
   (D.Lt ell mode true (D.history.identity a) old).L8=
     D.JD (D.history.oF hi hAuth) A.closed A.NA.NY.result a:= by
 rw [A.decode]
 exact D.y2 _ _ _ a old hOld
end Be.zF
end
noncomputable section
namespace Be.Fi
variable {N ell size: ℕ} {G M: SimpleGraph (Fin N)} {S: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (h: Fi S ids hi out hOut data)
   (hSize:∀r A,S.ND.state r=some A→ A.tree.vertices.card≤ size) (hS: 2≤ size)
   (mode: Bool) (R: SimpleGraph (Fin N))
   (hR: Matching ((S.tT ids hi hSize hS).Lv
     ((S.tT ids hi hSize hS).Lx ids data (IO.Fz ell mode))
     ((S.tT ids hi hSize hS).Dr ids data (IO.Fz ell mode))) R)
def GI: List (JZ G M ell mode):=
 (univ: Finset R.edgeSet).toList.map (h.Ix hSize hS mode R hR)
structure G3 (T: tI G M ell): Prop where
 pass:∃trace: List (Fin N ×Fin N),
   trace.length=matchingSize R∧ Dc mode trace S T
 support: Bl S T (JZ.MZ (h.GI hSize hS mode R hR))
 MO:∀e: R.edgeSet,(h.Ix hSize hS mode R hR e).M6 T∧
   (h.Ix hSize hS mode R hR e).Bc S.labels T
lemma oH:∃T,G3 h hSize hS mode R hR T:= by
 obtain ⟨T,es,hCount,hPass,hSupport,hOutcomes⟩:=h.nX hSize hS mode R hR
 exact ⟨T,⟨⟨es,hCount,hPass⟩,hSupport,hOutcomes⟩⟩
lemma nC (v: Fin N):
   v∈JZ.MZ (h.GI hSize hS mode R hR)↔
     ∃e: R.edgeSet,v∈(S.tT ids hi hSize hS).ET e.val:= by
 rw [JZ.HV]
 constructor
 · rintro ⟨A,hA,hVA⟩
   obtain ⟨e,he,hEq⟩:=List.mem_map.mp hA
   subst A
   exact ⟨e,hVA⟩
 · rintro ⟨e,hE⟩
   exact ⟨h.Ix hSize hS mode R hR e,List.mem_map.mpr
     ⟨e,Finset.mem_toList.mpr (mem_univ _),rfl⟩,hE⟩
end Be.Fi
end
noncomputable section
namespace Be.Fi
variable {N ell size: ℕ} {G M: SimpleGraph (Fin N)} {S T: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (h: Fi S ids hi out hOut data)
   (hSize:∀r A,S.ND.state r=some A→ A.tree.vertices.card≤ size) (hS: 2≤ size)
   (mode: Bool) (R: SimpleGraph (Fin N))
   (hR: Matching ((S.tT ids hi hSize hS).Lv
     ((S.tT ids hi hSize hS).Lx ids data (IO.Fz ell mode))
     ((S.tT ids hi hSize hS).Dr ids data (IO.Fz ell mode))) R)
   (W: G3 h hSize hS mode R hR T)
include W in
lemma G3.M9:∃es,M2 mode es S T:= by
 obtain ⟨es,_,hp⟩:=W.pass
 exact ⟨es,hp.Mh⟩
include W in
lemma Hh (u w: Fin N):
   (yO (S.tT ids hi hSize hS) ids data R ell mode u).labels (ids w)=T.labels (u,w):= by
 by_cases hOld: u∈S.Nm
 · rw [b3 _ ids data ell mode u ((h.Nm u).mpr hOld),h.labels]
   obtain ⟨es,hPass⟩:=W.M9
   exact (hPass.uH u w hOld).symm
 · by_cases hSel:∃e: R.edgeSet,u∈(S.tT ids hi hSize hS).ET e.val
   · obtain ⟨e,he⟩:=hSel
     let A:=h.Iw hSize hS mode R hR e
     obtain ⟨a,ha,hAU⟩:=A.region.IV u he hOld
     change A.task.embed.toFun a=u at hAU
     have hID: A.task.NI.history.identity a=ids u:=
       (A.Mz a).symm.trans (congrArg ids hAU)
     rw [p0 _ ids data ell mode hR e u he,←hID]
     have hd:=A.FF S.labels a (data u) (h.CY u hOld)
       (fun v=>by rw [h.labels,hAU]) w
     have hh: T.labels (A.task.embed.toFun a,w)=A.task.HG S.labels a w:=
       (W.MO e).2 a ha w
     rw [hAU] at hh
     exact hd.trans hh.symm
   · have hOutside: u∉JZ.MZ (h.GI hSize hS mode R hR):=
       fun hh=>hSel ((h.nC hSize hS mode R hR u).mp hh)
     rw [fM _ ids data ell mode u (by simpa only [not_exists] using hSel),h.labels]
     exact (W.support.D6 (u,w) hOutside).symm
include W in
lemma Fx (u: Fin N):
   (yO (S.tT ids hi hSize hS) ids data R ell mode u).Nm=true↔ u∈T.Nm:= by
 by_cases hOld: u∈S.Nm
 · have hNew: u∈T.Nm:=by obtain ⟨es,hPass⟩:=W.M9;exact hPass.In hOld
   rw [b3 _ ids data ell mode u ((h.Nm u).mpr hOld)]
   exact ⟨fun _=>hNew,fun _=>(h.Nm u).mpr hOld⟩
 · by_cases hSel:∃e: R.edgeSet,u∈(S.tT ids hi hSize hS).ET e.val
   · obtain ⟨e,he⟩:=hSel
     let A:=h.Iw hSize hS mode R hR e
     obtain ⟨a,ha,hAU⟩:=A.region.IV u he hOld
     change A.task.embed.toFun a=u at hAU
     have hID: A.task.NI.history.identity a=ids u:=
       (A.Mz a).symm.trans (congrArg ids hAU)
     rw [p0 _ ids data ell mode hR e u he,←hID]
     have hh: a∈A.NA.NY.result.Nm↔ A.task.embed.toFun a∈T.Nm:=
       (W.MO e).1.Nm a ha
     rw [hAU] at hh
     exact (A.Dx a (data u) (h.CY u hOld)).trans hh
   · have hOutside: u∉JZ.MZ (h.GI hSize hS mode R hR):=
       fun hh=>hSel ((h.nC hSize hS mode R hR u).mp hh)
     rw [fM _ ids data ell mode u (by simpa only [not_exists] using hSel)]
     exact (h.Nm u).trans (W.support.Cy u hOutside).symm
include W in
lemma mE (u: Fin N) (hu: u∉T.Nm):
   (yO (S.tT ids hi hSize hS) ids data R ell mode u).Nm=false:= by
 cases hb:(yO (S.tT ids hi hSize hS) ids data R ell mode u).Nm with
 | false => rfl
 | true => exact (hu ((h.Fx hSize hS mode R hR W u).mp hb)).elim
end Be.Fi
end
noncomputable section
namespace Be.Fi
variable {N ell size: ℕ} {G M: SimpleGraph (Fin N)} {S T: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (h: Fi S ids hi out hOut data)
   (hSize:∀r A,S.ND.state r=some A→ A.tree.vertices.card≤ size) (hS: 2≤ size)
   (mode: Bool) (R: SimpleGraph (Fin N))
   (hR: Matching ((S.tT ids hi hSize hS).Lv
     ((S.tT ids hi hSize hS).Lx ids data (IO.Fz ell mode))
     ((S.tT ids hi hSize hS).Dr ids data (IO.Fz ell mode))) R)
   (W: G3 h hSize hS mode R hR T)
include W in
lemma J8 (u v: Fin N):
   T.NV.Adj u v↔ G.Adj u v∧
     (yO (S.tT ids hi hSize hS) ids data R ell mode u).Nm=false∧
     (yO (S.tT ids hi hSize hS) ids data R ell mode v).Nm=false∧
     ids v∉(yO (S.tT ids hi hSize hS) ids data R ell mode u).ignored∧
     ids u∉(yO (S.tT ids hi hSize hS) ids data R ell mode v).ignored:= by
 obtain ⟨es,hPass⟩:=W.M9
 rw [(g7 _ ids data ell mode u).2.2,
   (g7 _ ids data ell mode v).2.2]
 constructor
 · intro hEdge
   have hOld:=(h.NV u v).mp (hPass.MF hEdge)
   have hAlive:=T.HK u v hEdge
   exact ⟨hOld.1,h.mE hSize hS mode R hR W u hAlive.1,
     h.mE hSize hS mode R hR W v hAlive.2,hOld.2.2.2⟩
 · rintro ⟨hEdge,hu,hv,hUV,hVU⟩
   have hU: u∉T.Nm:=by
     intro hh
     have hh':=(h.Fx hSize hS mode R hR W u).mpr hh
     rw [hu] at hh'
     cases hh'
   have hV: v∉T.Nm:=by
     intro hh
     have hh':=(h.Fx hSize hS mode R hR W v).mpr hh
     rw [hv] at hh'
     cases hh'
   exact (hPass.F7 u v).mpr ⟨(h.NV u v).mpr ⟨hEdge,
     h.CY u (fun hh=>hU (hPass.In hh)),
     h.CY v (fun hh=>hV (hPass.In hh)),hUV,hVU⟩,hU,hV⟩
include W in
lemma wM (u: Fin N) (B: tF)
   (hB:(yO (S.tT ids hi hSize hS) ids data R ell mode u).L8=some B):
   B.Represents T ids hi out hOut∧ ids u∈B.members:= by
 by_cases hOld: u∈S.Nm
 · rw [b3 _ ids data ell mode u ((h.Nm u).mpr hOld),
     h.vO u hOld] at hB
   cases hB
 · by_cases hSel:∃e: R.edgeSet,u∈(S.tT ids hi hSize hS).ET e.val
   · obtain ⟨e,he⟩:=hSel
     let A:=h.Iw hSize hS mode R hR e
     obtain ⟨a,ha,hAU⟩:=A.region.IV u he hOld
     change A.task.embed.toFun a=u at hAU
     have hID: A.task.NI.history.identity a=ids u:=
       (A.Mz a).symm.trans (congrArg ids hAU)
     rw [p0 _ ids data ell mode hR e u he,←hID] at hB
     have hBM:=(A.Hp a (data u) (h.CY u hOld)).symm.trans hB
     have hAuth: A.task.NI.history.Li G ids out:=
       IO.w7 _ h (IO.u2
         ((S.tT ids hi hSize hS).ET e.val) ids data)
     have hh:=A.task.NI.lI
       (A.task.NI.history.oF hi hAuth) A.closed A.NA.NY.result T ids hi out hOut hAuth
       (W.MO e).1.region.frame.present a B hBM
     exact ⟨hh.1,by simpa only [hID] using hh.2⟩
   · have hOutside: u∉JZ.MZ (h.GI hSize hS mode R hR):=
       fun hh=>hSel ((h.nC hSize hS mode R hR u).mp hh)
     rw [fM _ ids data ell mode u (by simpa only [not_exists] using hSel)] at hB
     exact h.jA W.support u hOutside B hB
end Be.Fi
end
noncomputable section
namespace Be.Fi
variable {N ell size: ℕ} {G M: SimpleGraph (Fin N)} {S T: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (h: Fi S ids hi out hOut data)
   (hSize:∀r A,S.ND.state r=some A→ A.tree.vertices.card≤ size) (hS: 2≤ size)
   (mode: Bool) (R: SimpleGraph (Fin N))
   (hR: Matching ((S.tT ids hi hSize hS).Lv
     ((S.tT ids hi hSize hS).Lx ids data (IO.Fz ell mode))
     ((S.tT ids hi hSize hS).Dr ids data (IO.Fz ell mode))) R)
   (W: G3 h hSize hS mode R hR T)
include W in
lemma oG (r: Fin N) (V: Lp G M r) (hV: T.ND.state r=some V):
   ∃B,∀v∈V.tree.vertices,
     (yO (S.tT ids hi hSize hS) ids data R ell mode v).L8=some B:= by
 by_cases hSel:∃e: R.edgeSet,r∈(S.tT ids hi hSize hS).ET e.val
 · obtain ⟨e,he⟩:=hSel
   let A:=h.Iw hSize hS mode R hR e
   have hOutcome: A.task.M6 T:=(W.MO e).1
   obtain ⟨a,Q,hQ,hAR⟩:=hOutcome.region.cover r he V hV
   change A.task.embed.toFun a=r at hAR
   subst r
   have hMap: Q.Nd A.task.embed=V:=
     Option.some.inj ((hOutcome.region.frame.present a Q hQ).symm.trans hV)
   let B: tF:=⟨A.task.NI.history,
     A.task.NI.history.oF hi (IO.w7 _ h
       (IO.u2 ((S.tT ids hi hSize hS).ET e.val) ids data)),
     A.closed,a,Q,A.NA.NY.result.complete a Q hQ⟩
   refine ⟨B,?_⟩
   intro v hv
   have hPre: v∈Q.tree.vertices.image A.task.embed.toFun:=by
     rw [←Q.Aj A.task.embed,hMap]
     exact hv
   obtain ⟨b,hb,hBV⟩:=mem_image.mp hPre
   have hAlive: b∉A.NA.NY.result.Nm:=A.NA.NY.result.k7 a Q hQ b hb
   have hOldAlive: b∉A.NA.state.Nm:=fun hh=>hAlive (A.NA.NY.In hh)
   have hRegion: v∈(S.tT ids hi hSize hS).ET e.val:=by
     have hh:=hOutcome.L1 b hOldAlive
     change A.task.embed.toFun b∈(S.tT ids hi hSize hS).ET e.val at hh
     rwa [hBV] at hh
   have hPhysical: v∉T.Nm:=T.k7 _ V hV v hv
   have hOld: v∉S.Nm:=by
     obtain ⟨es,hPass⟩:=W.M9
     exact fun hh=>hPhysical (hPass.In hh)
   have hID: A.task.NI.history.identity b=ids v:=
     (A.Mz b).symm.trans (congrArg ids hBV)
   rw [p0 _ ids data ell mode hR e v hRegion,←hID]
   exact (A.Hp b (data v) (h.CY v hOld)).trans
     (IO.sS _ _ A.closed A.NA.NY.result a b Q hQ hb)
 · have hOutside: r∉JZ.MZ (h.GI hSize hS mode R hR):=
     fun hh=>hSel ((h.nC hSize hS mode R hR r).mp hh)
   have hOld: S.ND.state r=some V:=(W.support.DO r hOutside).symm.trans hV
   obtain ⟨B,hB⟩:=h.El r V hOld
   refine ⟨B,?_⟩
   intro v hv
   have hNone:∀e: R.edgeSet,v∉(S.tT ids hi hSize hS).ET e.val:=by
     intro e he
     apply hSel
     refine ⟨e,?_⟩
     apply (S.tT ids hi hSize hS).g9 e.val v he r
     rw [S.iR ids hi hSize hS r V hOld v hv,
       S.iR ids hi hSize hS r V hOld r V.tree.MU]
   rw [fM _ ids data ell mode v hNone]
   exact hB v hv
end Be.Fi
end
noncomputable section
namespace Be.Fi
variable {N ell size: ℕ} {G M: SimpleGraph (Fin N)} {S T: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (h: Fi S ids hi out hOut data)
   (hSize:∀r A,S.ND.state r=some A→ A.tree.vertices.card≤ size) (hS: 2≤ size)
   (mode: Bool) (R: SimpleGraph (Fin N))
   (hR: Matching ((S.tT ids hi hSize hS).Lv
     ((S.tT ids hi hSize hS).Lx ids data (IO.Fz ell mode))
     ((S.tT ids hi hSize hS).Dr ids data (IO.Fz ell mode))) R)
   (W: G3 h hSize hS mode R hR T)
include W in
lemma Hi: ReportsMatching G ids
   (fun v=>let node:=yO (S.tT ids hi hSize hS) ids data R ell mode v
     if node.Nm then node.Md else node.Jf) T.Et:= by
 have hCanon:=tB.uZ G T.Et ids hi T.Eu.1.1
   (qJ.gP _ _ T.Eu.1)
 have hEq:(fun v=>let node:=yO (S.tT ids hi hSize hS) ids data R ell mode v
     if node.Nm then node.Md else node.Jf)=
     (fun v=>(tB.NW ids hi T.Et v).map ids):=by
   funext v
   dsimp only
   obtain ⟨es,hPass⟩:=W.M9
   by_cases hNew: v∈T.Nm
   · rw [(h.Fx hSize hS mode R hR W v).mpr hNew,if_pos rfl]
     by_cases hOld: v∈S.Nm
     · rw [b3 _ ids data ell mode v ((h.Nm v).mpr hOld)]
       have hh:=CA h.output hCanon v (fun w=>(hPass.u5 v w hOld).symm)
       simpa only [(h.Nm v).mpr hOld,if_true] using hh
     · have hSel:∃e: R.edgeSet,v∈(S.tT ids hi hSize hS).ET e.val:=by
         by_contra hh
         have hOutside: v∉JZ.MZ (h.GI hSize hS mode R hR):=
           fun hv=>hh ((h.nC hSize hS mode R hR v).mp hv)
         exact hOld ((W.support.Cy v hOutside).mp hNew)
       obtain ⟨e,he⟩:=hSel
       let A:=h.Iw hSize hS mode R hR e
       obtain ⟨a,ha,hAV⟩:=A.region.IV v he hOld
       change A.task.embed.toFun a=v at hAV
       have hID: A.task.NI.history.identity a=ids v:=
         (A.Mz a).symm.trans (congrArg ids hAV)
       rw [p0 _ ids data ell mode hR e v he,←hID]
       refine (congrArg Ln.Md (A.decode a (data v))).trans ?_
       refine (IO.y3 _ _ _ _ a (data v) (h.CY v hOld)).trans ?_
       have hh:=(W.MO e).1.Jv ids A.Mz _ hCanon a ha
       change A.task.NI.KM A.NA.NY.result a=
         (tB.NW ids hi T.Et (A.task.embed.toFun a)).map ids at hh
       rw [hAV] at hh
       exact hh
   · rw [h.mE hSize hS mode R hR W v hNew]
     simp only [Bool.false_eq_true,if_false]
     rw [(g7 _ ids data ell mode v).2.1,h.Jf]
     exact CA hOut hCanon v (fun w=>(T.Cp v w hNew).symm)
 rw [hEq]
 exact hCanon
end Be.Fi
end
noncomputable section
namespace Be.Fi
variable {N ell size: ℕ} {G M: SimpleGraph (Fin N)} {S T: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (h: Fi S ids hi out hOut data)
   (hSize:∀r A,S.ND.state r=some A→ A.tree.vertices.card≤ size) (hS: 2≤ size)
   (mode: Bool) (R: SimpleGraph (Fin N))
   (hR: Matching ((S.tT ids hi hSize hS).Lv
     ((S.tT ids hi hSize hS).Lx ids data (IO.Fz ell mode))
     ((S.tT ids hi hSize hS).Dr ids data (IO.Fz ell mode))) R)
   (W: G3 h hSize hS mode R hR T)
include W in
lemma Dl: Fi T ids hi out hOut
   (yO (S.tT ids hi hSize hS) ids data R ell mode):= by
 refine ⟨?_,?_,h.Hh hSize hS mode R hR W,h.Fx hSize hS mode R hR W,
   h.J8 hSize hS mode R hR W,h.wM hSize hS mode R hR W,
   h.oG hSize hS mode R hR W,h.Hi hSize hS mode R hR W⟩
 · intro v
   exact (g7 _ ids data ell mode v).1.trans (h.neighbors v)
 · intro v
   exact (g7 _ ids data ell mode v).2.1.trans (h.Jf v)
end Be.Fi
end
noncomputable section
namespace Be.Fi
variable {N ell size: ℕ} {G M: SimpleGraph (Fin N)} {S: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (h: Fi S ids hi out hOut data)
   (hSize:∀r A,S.ND.state r=some A→ A.tree.vertices.card≤ size) (hS: 2≤ size)
   {K: Type} (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K) (mode: Bool)
   (R: SimpleGraph (Fin N))
   (hR: ReportsMatching ((S.tT ids hi hSize hS).Lv
     ((S.tT ids hi hSize hS).Lx ids data (IO.Fz ell mode))
     ((S.tT ids hi hSize hS).Dr ids data (IO.Fz ell mode))) ids
     (execute A ((S.tT ids hi hSize hS).Lv
     ((S.tT ids hi hSize hS).Lx ids data (IO.Fz ell mode))
     ((S.tT ids hi hSize hS).Dr ids data (IO.Fz ell mode))) k ids
     (neighborIDs ((S.tT ids hi hSize hS).Lv
     ((S.tT ids hi hSize hS).Lx ids data (IO.Fz ell mode))
     ((S.tT ids hi hSize hS).Dr ids data (IO.Fz ell mode))) ids)) R)
include h hR in
lemma nI:∃T,(∃es,es.length=matchingSize R∧ Dc mode es S T)∧
   Fi T ids hi out hOut (execute (x6 A k size ell mode) G () ids data):= by
 obtain ⟨T,W⟩:=h.oH hSize hS mode R hR.1
 refine ⟨T,W.pass,?_⟩
 rw [gU (S.tT ids hi hSize hS) ids hi data
   (h.Gr hSize hS) A k ell mode R hR]
 exact h.Dl hSize hS mode R hR.1 W
end Be.Fi
end
noncomputable section
namespace Be
variable {N: ℕ}
namespace tE
variable {G: SimpleGraph (Fin N)} {s: ℕ} (P: tE G s)
lemma kQ (Lx: Fin N→ Fin N→ Prop) (hC: Symmetric Lx)
   (R: SimpleGraph (Fin N)) (B: ℕ)
   (hApprox: optimum (P.Lv Lx hC)≤ B*matchingSize R):
   ∃D: Finset (Fin N),D.card≤ 2*s*B*matchingSize R∧
     (∀u v,P.leader u=P.leader v→(u∈D↔ v∈D))∧
     ∀u v,G.Adj u v→ Lx u v→ P.leader u≠P.leader v→ u∈D∨ v∈D:= by
 obtain ⟨C,hSize,hCover⟩:=nS (P.Lv Lx hC)
 refine ⟨P.FE C,?_,P.oW C,?_⟩
 · have hCard:=P.tU C
   nlinarith [Nat.mul_le_mul_left s (hSize.trans (Nat.mul_le_mul_left 2 hApprox))]
 · intro u v hG hCand hNe
   have hAux:(P.Lv Lx hC).Adj (P.leader u) (P.leader v):=
     ⟨P.fixed u,P.fixed v,hNe,u,v,rfl,rfl,hG,hCand⟩
   simpa only [P.xN] using hCover _ _ hAux
end tE
lemma h3 {G M: SimpleGraph (Fin N)} {ell: ℕ}
   (states: ℕ→ tI G M ell) (es: ℕ→ List (Fin N ×Fin N))
   (mode: Bool) (hStep:∀t,Dc mode (es t) (states t) (states (t+1)))
   (D: ℕ→ Finset (Fin N)) (K B target: ℕ)
   (hK: 0<K) (hB: 0<B) (hTarget: 0<target)
   (hOpt: optimum G≤ B*matchingSize M)
   (hCover:∀t,(D t).card≤ K*(es t).length):
   ∃t<target*K*(2*ell+B),target*(D t).card≤ matchingSize M:= by
 let T:=target*K*(2*ell+B)
 have hT: 0<T:= by dsimp [T];positivity
 obtain ⟨t,ht,hSmall⟩:=eK states es mode hStep T hT
 have hSum: T*(es t).length≤(2*ell+B)*matchingSize M:= by nlinarith
 have hBound:= Nat.mul_le_mul_left T (hCover t)
 have hSumK:=Nat.mul_le_mul_left K hSum
 have hFactor: 0<K*(2*ell+B):= by positivity
 have hCancel:(K*(2*ell+B))*(target*(D t).card)≤
     (K*(2*ell+B))*matchingSize M:= by
   dsimp [T] at hBound hSumK
   nlinarith
 exact ⟨t,ht,(mul_le_mul_iff_right₀ hFactor).mp hCancel⟩
lemma eD {V: Type} [DecidableEq V] (D: Finset V)
   (pieces: Finset (Finset V)) (B T m: ℕ)
   (hUnion: D⊆pieces.biUnion id) (hCount: pieces.card≤ T)
   (hEach:∀E∈pieces,B*T*E.card≤ m): B*D.card≤ m:= by
 by_cases hT: T=0
 · have hEmpty: pieces=∅:=card_eq_zero.mp (by omega)
   have hDEmpty: D=∅:=eq_empty_iff_forall_notMem.mpr (fun v hv=>by simpa [hEmpty] using hUnion hv)
   simp [hDEmpty]
 · have hD: D.card≤∑E∈pieces,E.card:=(card_le_card hUnion).trans card_biUnion_le
   have hSum:=sum_le_sum hEach
   have hTotal: B*T*(∑E∈pieces,E.card)≤ T*m:= by
     have hCountM:=Nat.mul_le_mul_right m hCount
     simp only [←mul_sum,sum_const,smul_eq_mul] at hSum
     exact hSum.trans hCountM
   have hMult:=Nat.mul_le_mul_left (B*T) hD
   have hCancel: T*(B*D.card)≤ T*m:= by nlinarith
   exact (mul_le_mul_iff_right₀ (by omega: 0<T)).mp hCancel
end Be
end
noncomputable section
namespace Be
variable {K: Type}
def Ms (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   {N: ℕ} (H: SimpleGraph (Fin N)) (ids: Fin N→ ℕ) (B: ℕ): Prop:=
 ∃R,ReportsMatching H ids (execute A H k ids (neighborIDs H ids)) R∧ optimum H≤ B*matchingSize R
namespace Fi
variable {N ell size: ℕ} {G M: SimpleGraph (Fin N)} {S: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (h: Fi S ids hi out hOut data)
   (hSize:∀r V,S.ND.state r=some V→ V.tree.vertices.card≤ size) (hS: 2≤ size)
   (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K) (mode: Bool) (B: ℕ)
include h in
lemma x2
   (hOracle: Ms A k ((S.tT ids hi hSize hS).Lv
     ((S.tT ids hi hSize hS).Lx ids data (IO.Fz ell mode))
     ((S.tT ids hi hSize hS).Dr ids data (IO.Fz ell mode))) ids B):
   ∃(T: tI G M ell) (es: List (Fin N ×Fin N)) (D: Finset (Fin N)),
     Dc mode es S T∧
     Fi T ids hi out hOut (execute (x6 A k size ell mode) G () ids data)∧
     D.card≤ 2*size*B*es.length∧
     (∀u v,G.Adj u v→
       (S.tT ids hi hSize hS).Lx ids data (IO.Fz ell mode) u v→
       (S.tT ids hi hSize hS).leader u≠(S.tT ids hi hSize hS).leader v→
         u∈D∨ v∈D):= by
 obtain ⟨R,hR,hApprox⟩:=hOracle
 obtain ⟨D,hD,hClosed,hCover⟩:=(S.tT ids hi hSize hS).kQ
   ((S.tT ids hi hSize hS).Lx ids data (IO.Fz ell mode))
   ((S.tT ids hi hSize hS).Dr ids data (IO.Fz ell mode)) R B hApprox
 obtain ⟨T,⟨es,hCount,hPass⟩,hEncoding⟩:=h.nI hSize hS A k mode R hR
 exact ⟨T,es,D,hPass,hEncoding,by simpa only [hCount] using hD,hCover⟩
end Fi
end Be
end
noncomputable section
namespace Be
variable {K: Type}
def qH (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   {N: ℕ} (G: SimpleGraph (Fin N)) (ids: Fin N→ ℕ) (size B: ℕ): Prop:=
 ∀(P: tE G size) (data: Fin N→ Ln) (ell: ℕ) (mode: Bool),
   Ms A k (P.Lv (P.Lx ids data (IO.Fz ell mode))
     (P.Dr ids data (IO.Fz ell mode))) ids B
structure Da {N ell: ℕ} {G M: SimpleGraph (Fin N)}
   (S0: tI G M ell) (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (out: Fin N→ Option ℕ) (hOut: ReportsMatching G ids out M) (mode: Bool) where
 state: tI G M ell
 data: Fin N→ Ln
 encoding: Fi state ids hi out hOut data
 trace: List (Fin N ×Fin N)
 pass: Dc mode trace S0 state
namespace Da
variable {N ell size B: ℕ} {G M: SimpleGraph (Fin N)} {S0: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {mode: Bool}
   (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K) (hS: 2≤ size)
   (hBound:∀U es,M2 mode es S0 U→∀r V,U.ND.state r=some V→ V.tree.vertices.card≤ size)
   (hOracle: qH A k G ids size B)
   (X: Da S0 ids hi out hOut mode)
def Mf:∀r V,X.state.ND.state r=some V→ V.tree.vertices.card≤ size:=
 hBound X.state X.trace X.pass.Mh
structure Mt where
 state: tI G M ell
 edges: List (Fin N ×Fin N)
 omitted: Finset (Fin N)
 pass: Dc mode edges X.state state
 encoding: Fi state ids hi out hOut (execute (x6 A k size ell mode) G () ids X.data)
 count: omitted.card≤ 2*size*B*edges.length
 cover:∀u v,G.Adj u v→
   (X.state.tT ids hi (X.Mf hBound) hS).Lx ids X.data (IO.Fz ell mode) u v→
   (X.state.tT ids hi (X.Mf hBound) hS).leader u≠
     (X.state.tT ids hi (X.Mf hBound) hS).leader v→ u∈omitted∨ v∈omitted
def MY: X.Mt (B:=B) A k hS hBound:=
 Classical.choice (by
   obtain ⟨T,es,D,hPass,hEncoding,hCount,hCover⟩:=X.encoding.x2 (X.Mf hBound) hS A k mode B
     (hOracle (X.state.tT ids hi (X.Mf hBound) hS) X.data ell mode)
   exact ⟨⟨T,es,D,hPass,hEncoding,hCount,hCover⟩⟩)
def next: Da S0 ids hi out hOut mode where
 state:=(X.MY A k hS hBound hOracle).state
 data:=execute (x6 A k size ell mode) G () ids X.data
 encoding:=(X.MY A k hS hBound hOracle).encoding
 trace:=X.trace++(X.MY A k hS hBound hOracle).edges
 pass:=X.pass.append (X.MY A k hS hBound hOracle).pass
end Da
variable {N ell size B: ℕ} {G M: SimpleGraph (Fin N)} {S0: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {mode: Bool}
   (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K) (hS: 2≤ size)
   (hBound:∀U es,M2 mode es S0 U→∀r V,U.ND.state r=some V→ V.tree.vertices.card≤ size)
   (hOracle: qH A k G ids size B)
   (data0: Fin N→ Ln) (h0: Fi S0 ids hi out hOut data0)
def L2: ℕ→ Da S0 ids hi out hOut mode
 | 0=>⟨S0,data0,h0,[],Dc.nil S0⟩
 | t+1=>(L2 t).next A k hS hBound hOracle
lemma Es (t: ℕ):(L2 A k hS hBound hOracle data0 h0 t).data=
   execute (AD A k size ell mode t) G () ids data0:= by
 have hConfig:∀t,(L2 A k hS hBound hOracle data0 h0 t).data=
     IM.Dw (fun _=>x6 A k size ell mode) G ids data0 t:=by
   intro t
   induction t with
   | zero => rfl
   | succ t ih =>
     change execute (x6 A k size ell mode) G () ids
       (L2 A k hS hBound hOracle data0 h0 t).data=_
     rw [ih]
     rfl
 rw [hConfig]
 funext v
 exact (IM.Gy (fun _=>x6 A k size ell mode) G ids data0 t v).symm
end Be
end
noncomputable section
namespace Be.IO
lemma x1 (D: IO) (ell: ℕ) (mode: Bool) (x y: ℕ)
   (h: D.omission ell mode x y): D.Mx ell mode x y∨ D.Mx ell mode y x:= by
 obtain ⟨U,hU,u,v,hUX,hVY,hCross,hReq⟩:=h
 cases mode with
 | true =>
   change Nonempty (y7 U u v)∨ Nonempty (y7 U v u) at hReq
   rcases hReq with hReq|hReq
   · exact Or.inl ⟨U,hU,u,v,hUX,hVY,hCross,JQ U true u v (Or.inr ⟨rfl,hReq⟩)⟩
   · exact Or.inr ⟨U,hU,v,u,hVY,hUX,hCross.symm,JQ U true v u (Or.inr ⟨rfl,hReq⟩)⟩
 | false =>
   change U.Bd u v false∨ U.Bd v u false at hReq
   rcases hReq with hReq|hReq
   · exact Or.inl ⟨U,hU,u,v,hUX,hVY,hCross,JQ U false u v (Or.inl hReq)⟩
   · exact Or.inr ⟨U,hU,v,u,hVY,hUX,hCross.symm,JQ U false v u (Or.inl hReq)⟩
end Be.IO
namespace Be.Fi
variable {N ell size: ℕ} {G M: SimpleGraph (Fin N)} {S: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (h: Fi S ids hi out hOut data)
   (hSize:∀r V,S.ND.state r=some V→ V.tree.vertices.card≤ size) (hS: 2≤ size)
include h in
lemma u1 (mode: Bool) (u v: Fin N)
   (hE: s(u,v)∈(if mode then S.tZ else S.l9)):
   G.Adj u v∧
     (S.tT ids hi hSize hS).Lx ids data (IO.Fz ell mode) u v∧
     (S.tT ids hi hSize hS).leader u≠(S.tT ids hi hSize hS).leader v:= by
 have hReq:=(S.pT ids hi hSize hS mode u v).mpr hE
 have hLive: S.NV.Adj u v:=by
   cases mode with
   | true =>
     have hh: Nonempty (y7 S u v)∨ Nonempty (y7 S v u):=hReq.2
     exact hh.elim (fun hh=>hh.some.IY) (fun hh=>hh.some.IY.symm)
   | false =>
     have hh: S.Bd u v false∨ S.Bd v u false:=hReq.2
     rcases hh with hh|hh
     · exact hh.some.val.IY
     · exact hh.some.val.IY.symm
 refine ⟨S.MF hLive,?_,hReq.1⟩
 have hOmit:=(h.mG hSize hS mode u v).mpr hE
 have hWork:=IO.x1 _ ell mode (ids u) (ids v) hOmit
 change IO.Mx
   ((S.tT ids hi hSize hS).NI ids data u∪
     (S.tT ids hi hSize hS).NI ids data v) ell mode (ids u) (ids v)∨
   IO.Mx
   ((S.tT ids hi hSize hS).NI ids data v∪
     (S.tT ids hi hSize hS).NI ids data u) ell mode (ids v) (ids u)
 exact hWork.imp id (fun hh=>by rwa [union_comm] at hh)
end Be.Fi
namespace Be.Da
variable {K: Type} {N ell size B: ℕ} {G M: SimpleGraph (Fin N)} {S0: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {mode: Bool}
   (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K) (hS: 2≤ size)
   (hBound:∀U es,M2 mode es S0 U→∀r V,U.ND.state r=some V→ V.tree.vertices.card≤ size)
   (hOracle: qH A k G ids size B)
   (X: Da S0 ids hi out hOut mode)
include X in
lemma Er:∀u v,s(u,v)∈(if mode then X.state.tZ else X.state.l9)→
   u∈(X.MY A k hS hBound hOracle).omitted∨ v∈(X.MY A k hS hBound hOracle).omitted:= by
 intro u v hE
 obtain ⟨hG,hCandidate,hCross⟩:=X.encoding.u1 (X.Mf hBound) hS mode u v hE
 exact (X.MY A k hS hBound hOracle).cover u v hG hCandidate hCross
end Be.Da
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
namespace tI
def Fh (S T: tI G M ell) (D: Finset (Fin N)): Prop:=
 ∀u v,S.NV.Adj u v→ u∉T.Nm→ v∉T.Nm→ u∉D→ v∉D→ T.NV.Adj u v
lemma Fh.refl (S: tI G M ell): S.Fh S ∅:= by
 intro u v h _ _ _ _;exact h
lemma Fh.trans {S T U: tI G M ell} {D E: Finset (Fin N)}
   (hST: S.Fh T D) (hTU: T.Fh U E)
   (hRemoved: T.Nm⊆U.Nm): S.Fh U (D∪E):= by
 intro u v hLive hu hv huDE hvDE
 have huD: u∉D:=fun h=>huDE (mem_union_left _ h)
 have hvD: v∉D:=fun h=>hvDE (mem_union_left _ h)
 have huE: u∉E:=fun h=>huDE (mem_union_right _ h)
 have hvE: v∉E:=fun h=>hvDE (mem_union_right _ h)
 exact hTU u v (hST u v hLive (fun h=>hu (hRemoved h)) (fun h=>hv (hRemoved h)) huD hvD)
   hu hv huE hvE
end tI
lemma M3.Er {S T: tI G M ell} {mode: Bool} {x y: Fin N}
   (h: M3 mode x y S T): S.Fh T ∅:= by
 cases h with
 | augmentation R hFlag =>
   intro u v hLive hu hv _ _
   have huD: u∉R.left.tree.vertices∪R.right.tree.vertices:= fun h=>hu (mem_union_right _ h)
   have hvD: v∉R.left.tree.vertices∪R.right.tree.vertices:= fun h=>hv (mem_union_right _ h)
   exact ⟨hLive,huD,hvD⟩
 | extension hMode R hNo A => cases A<;> exact tI.Fh.refl _
 | skip hNo hExt => exact tI.Fh.refl _
lemma M2.Er {S T: tI G M ell} {mode: Bool}
   {es: List (Fin N ×Fin N)} (h: M2 mode es S T): S.Fh T ∅:= by
 induction h with
 | nil S => exact tI.Fh.refl S
 | cons step rest ih => simpa only [union_empty] using step.Er.trans ih rest.In
lemma pN (S: tI G M ell) (E: Finset (Sym2 (Fin N)))
   (hM:∀u v,M.Adj u v→ s(u,v)∉E)
   (hMemory:∀r R,S.ND.state r=some R→∀u v,(u,v)∈R.tree.NS→ s(u,v)∉E)
   (D: Finset (Fin N)) (hCover:∀u v,s(u,v)∈E→ u∈D∨ v∈D):
   S.Fh (S.DH E hM hMemory) D:= by
 intro u v hLive hu hv huD hvD
 refine ⟨hLive,?_⟩
 intro hE
 rcases hCover u v hE with h|h
 · exact huD h
 · exact hvD h
lemma pJ (states: ℕ→ tI G M ell) (D: ℕ→ Finset (Fin N))
   (hCover:∀t,(states t).Fh (states (t+1)) (D t))
   (hRemoved:∀t,(states t).Nm⊆(states (t+1)).Nm) (T: ℕ):
   (states 0).Fh (states T) ((range T).biUnion D):= by
 induction T with
 | zero => simpa using tI.Fh.refl (states 0)
 | succ T ih =>
   have h:=ih.trans (hCover T) (hRemoved T)
   simpa only [range_add_one,biUnion_insert,biUnion_singleton,union_comm] using h
end Be
end
noncomputable section
namespace Be
namespace tE
variable {N size: ℕ} {G: SimpleGraph (Fin N)} (P: tE G size)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (data: Fin N→ Ln)
   (hTags:∀v,(data v).leader (ids v)=ids (P.leader v)) (ell: ℕ)
include hi hTags in
lemma d5 (v: Fin N):
   execute (rM size ell) G () ids data v=
     IO.Lt (P.NI ids data v) ell true false (ids v) (data v):= by
 unfold execute rM
 rw [C7.A4,C7.FS]
 have hInput:(fun w=>((data w).leader (ids w),data w))=(fun w=>(ids (P.leader w),data w)):=by
   funext w
   exact congrArg (fun j=>(j,data w)) (hTags w)
 rw [hInput,P.I0 ids hi data v]
 rfl
end tE
namespace Fi
variable {N ell size: ℕ} {G M: SimpleGraph (Fin N)} {S: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (h: Fi S ids hi out hOut data)
   (hSize:∀r V,S.ND.state r=some V→ V.tree.vertices.card≤ size) (hS: 2≤ size)
include h in
lemma kS: execute (rM size ell) G () ids data=
   (h.D4 hSize hS).update:= by
 funext v
 rw [(S.tT ids hi hSize hS).d5 ids hi data
   (h.Gr hSize hS) ell v]
 by_cases hWork: Nonempty (IO.JR
   ((S.tT ids hi hSize hS).NI ids data v) ell true false)
 · let r:(S.tT ids hi hSize hS).Fc ids data ell:=
     ⟨(S.tT ids hi hSize hS).leader v,(S.tT ids hi hSize hS).fixed v,
       by rwa [←(S.tT ids hi hSize hS).L3 ids data v
         ((S.tT ids hi hSize hS).leader v)
         ((S.tT ids hi hSize hS).fixed v).symm]⟩
   have hV: v∈(h.D4 hSize hS).region r:=by
     change v∈univ.filter _
     exact mem_filter.mpr ⟨mem_univ _,((S.tT ids hi hSize hS).fixed v).symm⟩
   rw [(h.D4 hSize hS).Mj r v hV]
   change IO.Lt ((S.tT ids hi hSize hS).NI ids data v) ell true false (ids v) (data v)=
     IO.Lt ((S.tT ids hi hSize hS).NI ids data ((S.tT ids hi hSize hS).leader v)) ell true false (ids v) (data v)
   rw [(S.tT ids hi hSize hS).L3 ids data v
     ((S.tT ids hi hSize hS).leader v) ((S.tT ids hi hSize hS).fixed v).symm]
 · have hOutside:∀r:(S.tT ids hi hSize hS).Fc ids data ell,
       v∉(h.D4 hSize hS).region r:=by
     intro r hV
     have hSame:(S.tT ids hi hSize hS).leader v=
         (S.tT ids hi hSize hS).leader r.val:=(mem_filter.mp hV).2
     have hPackets:=(S.tT ids hi hSize hS).L3 ids data v r.val hSame
     exact hWork (hPackets.symm ▸r.property.2)
   rw [(h.D4 hSize hS).E4 v hOutside]
   have hNone: IO.Kc ((S.tT ids hi hSize hS).NI ids data v) ell true false=none:=by
     unfold IO.Kc
     rw [dif_neg hWork]
   unfold IO.Lt
   split_ifs<;> simp only [hNone]
end Fi
end Be
end
noncomputable section
namespace Be.IO.NR
variable {D: IO} {ell: ℕ} {U: tI D.history.graph D.history.MG ell}
   {mode: Bool} {x y: Fin D.history.keys.card}
lemma Hc (W: NR U mode x y)
   (hUnique:∀a A,U.ND.state a=some A→∀b B,U.ND.state b=some B→ a=b):
   ∀a A,W.result.ND.state a=some A→ A.extended=true:= by
 cases W with
 | augmentation R hFlag => exact (R.distinct (hUnique _ _ R.HJ _ _ R.GE)).elim
 | extension hMode R hNo C =>
   intro a A hA
   obtain ⟨B,hB⟩:=(C.JG a).mp ⟨A,hA⟩
   have hRoot:=hUnique a B hB R.root R.state R.present
   subst a
   obtain ⟨Q,hQ,_,_,hExtended,_⟩:=C.EG
   have hAQ: A=Q:=Option.some.inj (hA.symm.trans hQ)
   rw [hAQ]
   exact hExtended
end Be.IO.NR
namespace Be.Fi
variable {N ell size: ℕ} {G M: SimpleGraph (Fin N)} {S: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (h: Fi S ids hi out hOut data)
   (hSize:∀r V,S.ND.state r=some V→ V.tree.vertices.card≤ size) (hS: 2≤ size)
include h in
lemma m5 (i:(S.tT ids hi hSize hS).Fc ids data ell)
   (a: Fin ((h.D4 hSize hS).NI i).history.keys.card)
   (V: Lp ((h.D4 hSize hS).NI i).history.graph
     ((h.D4 hSize hS).NI i).history.MG a)
   (hV:((h.D4 hSize hS).Na i).NA.state.ND.state a=some V):
   ((h.D4 hSize hS).Na i).task.embed.toFun a=i.val:= by
 let A:=(h.D4 hSize hS).Na i
 have hPresent:=A.region.frame.present a V hV
 have hMember:=A.region.image a (A.NA.state.vI a V hV)
 have hRoot:=S.iR ids hi hSize hS _ (V.Nd A.task.embed) hPresent _
   (V.Nd A.task.embed).tree.MU
 have hBlock:(S.tT ids hi hSize hS).leader (A.task.embed.toFun a)=
     (S.tT ids hi hSize hS).leader i.val:=(mem_filter.mp hMember).2
 exact hRoot.symm.trans (hBlock.trans i.property.1)
include h in
lemma m3 (i:(S.tT ids hi hSize hS).Fc ids data ell):
   let A:=(h.D4 hSize hS).Na i
   ∀a V,A.NA.NY.result.ND.state a=some V→ V.extended=true:= by
 dsimp only
 apply IO.NR.Hc
 intro a V hV b Q hQ
 apply ((h.D4 hSize hS).Na i).task.embed.injective
 exact (h.m5 hSize hS i a V hV).trans
   (h.m5 hSize hS i b Q hQ).symm
end Be.Fi
end
noncomputable section
namespace Be.IO
variable {N ell s: ℕ} {G M: SimpleGraph (Fin N)} (S: tI G M ell)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (hSize:∀r R,S.ND.state r=some R→ R.tree.vertices.card≤ s) (hS: 2≤ s)
   (out: Fin N→ Option ℕ) (hOut: ReportsMatching G ids out M)
   (data: Fin N→ Ln) (h: Fi S ids hi out hOut data)
   (D: IO) (hD:∀z∈D,∃v,z=(ids v,data v))
   (hSat: D.Saturated (S.tT ids hi hSize hS) ids)
include h hD hSat in
lemma m2 (mode: Bool) (x y: Fin N) (hX: ids x∈D.keys) (hY: ids y∈D.keys)
   (hLive: S.NV.Adj x y)
   (hRequest: S.Bd x y mode∨(mode=true∧ Nonempty (y7 S x y))):
   Nonempty (JR D ell mode false):= by
 obtain ⟨hClosed,U,hView,hEmbed⟩:=D.ER S ids hi hSize hS hSat out hOut data h hD
 let E:=D.history.embedding (D.w7 h hD) hi hOut hClosed
 obtain ⟨u,hUX,hU⟩:=GY S ids hi out hOut data h D hD hClosed x hX
 obtain ⟨v,hVY,hV⟩:=GY S ids hi out hOut data h D hD hClosed y hY
 have hLocalU: u∈D.alive:=by
   apply (D.Ls h hD hClosed u).mpr
   exact ⟨hU.symm ▸hX,hUX.symm ▸(S.HK x y hLive).1⟩
 have hLocalV: v∈D.alive:=by
   apply (D.Ls h hD hClosed v).mpr
   exact ⟨hV.symm ▸hY,hVY.symm ▸(S.HK x y hLive).2⟩
 have hLocalLive: U.NV.Adj u v:=by
   rw [(D.Lf ell U hView).NV]
   apply (D.F6 h hD hClosed u v).mpr
   exact ⟨hLocalU,hLocalV,by rw [hUX,hVY];exact hLive⟩
 have hLocalRequest: U.Bd u v mode∨(mode=true∧ Nonempty (y7 U u v)):=by
   rcases hRequest with hAug|⟨hMode,⟨R⟩⟩
   · exact Or.inl (hEmbed.oE u v mode hLocalLive (by rw [hUX,hVY];exact hAug))
   · exact Or.inr ⟨hMode,hEmbed.w2 u v hLocalLive (by rw [hUX,hVY];exact R)⟩
 obtain ⟨W⟩:=JQ U mode u v hLocalRequest
 exact ⟨⟨U,hView,u,v,fun h=>Bool.noConfusion h,W⟩⟩
end Be.IO
end
noncomputable section
namespace Be.Fi
variable {N ell size: ℕ} {G M: SimpleGraph (Fin N)} {S T: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (h: Fi S ids hi out hOut data)
   (hSize:∀r V,S.ND.state r=some V→ V.tree.vertices.card≤ size) (hS: 2≤ size)
include h in
lemma m4 {x y: Fin N} (R: y7 S x y)
   (hOwn: S.ND.Mm R.root y):
   Nonempty (IO.JR ((S.tT ids hi hSize hS).NI ids data R.root) ell true false):= by
 let P:=S.tT ids hi hSize hS
 let D: IO:=P.NI ids data R.root
 have hX: ids x∈D.keys:=by
   apply (P.Ex ids hi data R.root x).mpr
   exact (S.iR ids hi hSize hS R.root R.state R.present x R.K5).trans
     (S.iR ids hi hSize hS R.root R.state R.present R.root R.state.tree.MU).symm
 have hY: ids y∈D.keys:=by
   obtain ⟨V,hV,hYV⟩:=hOwn
   apply (P.Ex ids hi data R.root y).mpr
   exact (S.iR ids hi hSize hS R.root V hV y hYV).trans
     (S.iR ids hi hSize hS R.root V hV R.root V.tree.MU).symm
 exact D.m2 S ids hi hSize hS out hOut data h
   (IO.u2 (P.block R.root) ids data)
   (IO.AF P ids hi data R.root) true x y hX hY R.IY (Or.inr ⟨rfl,⟨R⟩⟩)
include h in
lemma kR (W:(h.D4 hSize hS).Witness T)
   (hFlags: S.zE): T.iE:= by
 intro x y R hOwn
 by_cases hSel:∃i:(S.tT ids hi hSize hS).Fc ids data ell,
     R.root∈(h.D4 hSize hS).region i
 · obtain ⟨i,hi⟩:=hSel
   let A:=(h.D4 hSize hS).Na i
   obtain ⟨a,V,hV,hAR⟩:=(W.MO i).1.region.cover R.root hi R.state R.present
   change A.task.embed.toFun a=R.root at hAR
   have hExt:=h.m3 hSize hS i a V hV
   have hMapped:=(W.MO i).1.region.frame.present a V hV
   change T.ND.state (A.task.embed.toFun a)=some (V.Nd A.task.embed) at hMapped
   have hh:(T.ND.state (A.task.embed.toFun a)).map (fun Z=>Z.extended)=some true:=by
     rw [hMapped]
     change some V.extended=some true
     rw [hExt]
   rw [hAR,R.present] at hh
   have he: R.state.extended=true:=Option.some.inj hh
   rw [R.H9] at he
   cases he
 · have hOutside: R.root∉JZ.MZ (h.D4 hSize hS).tasks:=
     fun hh=>hSel (((h.D4 hSize hS).HV R.root).mp hh)
   have hOldState: S.ND.state R.root=some R.state:=
     (W.support.DO R.root hOutside).symm.trans R.present
   have hMod: R.state.modified=false:=by
     cases hb: R.state.modified with
     | false => rfl
     | true => have hh:=hFlags _ _ hOldState hb;rw [R.H9] at hh;cases hh
   obtain ⟨es,hPass⟩:=W.M9
   obtain ⟨Q,hQR⟩:=hPass.jT R hMod
   obtain ⟨B,hB,hBm,hVertices,hGraph,hCache⟩:=hPass.lY R.root R.state R.present hMod
   obtain ⟨V,hV,hy⟩:=hOwn
   have hVR: V=R.state:=Option.some.inj (hV.symm.trans R.present)
   subst V
   have hQOwn: S.ND.Mm Q.root y:=by rw [hQR];exact ⟨B,hB,hVertices hy⟩
   have hWork:=h.m4 hSize hS Q hQOwn
   let i:(S.tT ids hi hSize hS).Fc ids data ell:=
     ⟨Q.root,S.iR ids hi hSize hS Q.root Q.state Q.present Q.root Q.state.tree.MU,hWork⟩
   apply hSel
   refine ⟨i,?_⟩
   change R.root∈univ.filter _
   exact mem_filter.mpr ⟨mem_univ _,show (S.tT ids hi hSize hS).leader R.root=
     (S.tT ids hi hSize hS).leader Q.root from congrArg _ hQR.symm⟩
include h hSize hS in
lemma i3 (hFlags: S.zE):
   ∃T es,Dc true es S T∧ T.iE∧
     Fi T ids hi out hOut (execute (rM size ell) G () ids data):= by
 obtain ⟨T,W⟩:=(h.D4 hSize hS).E6
 obtain ⟨es,hPass⟩:=W.pass
 refine ⟨T,es,hPass,h.kR hSize hS W hFlags,?_⟩
 rw [h.kS hSize hS]
 exact (h.D4 hSize hS).Dl h W
end Be.Fi
end
noncomputable section
namespace Be
variable {K: Type} {N ell size B: ℕ} {G M: SimpleGraph (Fin N)} {S0: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {mode: Bool}
   (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K) (hS: 2≤ size)
   (hBound:∀U es,M2 mode es S0 U→∀r V,U.ND.state r=some V→ V.tree.vertices.card≤ size)
   (hOracle: qH A k G ids size B)
   (data0: Fin N→ Ln) (h0: Fi S0 ids hi out hOut data0)
include h0 hS hBound hOracle in
lemma Co (target: ℕ) (hTarget: 0<target) (hB: 0<B)
   (hOpt: optimum G≤ B*matchingSize M) (hClosed: mode=true→ S0.iE):
   ∃(j: ℕ) (T: tI G M ell) (es: List (Fin N ×Fin N)) (D: Finset (Fin N)),
     j<target*(2*size*B)*(2*ell+B)∧ target*D.card≤ matchingSize M∧
     y5 mode es S0 T∧ S0.Fh T D∧
     Fi T ids hi out hOut
       (execute (Mg (AD A k size ell mode j) (yE size ell mode)) G () ids data0):= by
 let run:=L2 A k hS hBound hOracle data0 h0
 let states:=fun t=>(run t).state
 let edges:=fun t=>((run t).MY A k hS hBound hOracle).edges
 let omitted:=fun t=>((run t).MY A k hS hBound hOracle).omitted
 have hSteps:∀t,Dc mode (edges t) (states t) (states (t+1)):=by
   intro t
   exact ((run t).MY A k hS hBound hOracle).pass
 have hCover:∀t,(omitted t).card≤(2*size*B)*(edges t).length:=by
   intro t
   exact ((run t).MY A k hS hBound hOracle).count
 obtain ⟨j,hJ,hSmall⟩:=h3 states edges mode hSteps omitted (2*size*B) B target
   (by positivity) hB hTarget hOpt hCover
 let X:=run j
 let T:=if mode then X.state.Cs else X.state.vL
 have hCertified: y5 mode X.trace S0 T:=by
   cases mode with
   | true => exact X.pass.Mh.qW (hClosed rfl)
   | false => exact X.pass.Mh.Bt
 have hPruneCover: X.state.Fh T (omitted j):=by
   cases mode with
   | true =>
     exact pN X.state X.state.tZ X.state.cB
       X.state.e1 (omitted j) (X.Er A k hS hBound hOracle)
   | false =>
     exact pN X.state X.state.l9 X.state.bA
       X.state.b6 (omitted j) (X.Er A k hS hBound hOracle)
 have hTotalCover: S0.Fh T (omitted j):=by
   have hh:=X.pass.Mh.Er.trans hPruneCover (by cases mode<;> exact subset_refl _)
   simpa only [empty_union] using hh
 refine ⟨j,T,X.trace,omitted j,hJ,hSmall,hCertified,hTotalCover,?_⟩
 have hEncode:=X.encoding.nN (X.Mf hBound) hS mode
 have hInput: X.data=execute (AD A k size ell mode j) G () ids data0:=
   Es A k hS hBound hOracle data0 h0 j
 rw [AZ,←hInput]
 exact hEncode
end Be
end
noncomputable section
namespace Be
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)}
lemma M2.EX {mode: Bool} {es fs: List (Fin N ×Fin N)}
   {S U T: tI G M ell} (h: M2 mode es S U)
   (hC: y5 mode fs U T): y5 mode (es++fs) S T where
 Np:=by
   obtain ⟨V,hV,hPrune⟩:=hC.Np
   exact ⟨V,h.append hV,hPrune⟩
 KI:=hC.KI
 MH:=hC.MH
namespace Fi
variable {K: Type} {size B: ℕ} {S0: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data0: Fin N→ Ln}
   (h0: Fi S0 ids hi out hOut data0)
   (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K) (hS: 2≤ size) (mode: Bool)
   (hBound:∀U es,M2 mode es S0 U→∀r V,U.ND.state r=some V→ V.tree.vertices.card≤ size)
   (hOracle: qH A k G ids size B)
include h0 hS hBound hOracle in
lemma GP (target: ℕ) (hTarget: 0<target) (hB: 0<B)
   (hOpt: optimum G≤ B*matchingSize M) (hFlags: mode=true→ S0.zE):
   ∃(j: ℕ) (T: tI G M ell) (es: List (Fin N ×Fin N)) (D: Finset (Fin N)),
     j<target*(2*size*B)*(2*ell+B)∧ target*D.card≤ matchingSize M∧
     y5 mode es S0 T∧ S0.Fh T D∧
     Fi T ids hi out hOut (execute (IC A k size ell mode j) G () ids data0):= by
 let pre:=if mode then rM size ell else C7.pointwise (fun _ z=>z)
 have hPre:∃(U: tI G M ell) (es: List (Fin N ×Fin N)),
     Dc mode es S0 U∧(mode=true→ U.iE)∧
     Fi U ids hi out hOut (execute pre G () ids data0):=by
   cases mode with
   | true =>
     obtain ⟨U,es,hPass,hClosed,hEncoding⟩:=h0.i3 (hBound S0 [] (M2.nil S0)) hS (hFlags rfl)
     exact ⟨U,es,hPass,fun _=>hClosed,hEncoding⟩
   | false => exact ⟨S0,[],Dc.nil _,fun hh=>Bool.noConfusion hh,h0⟩
 obtain ⟨U,preEdges,hPrePass,hClosed,hPreEncoding⟩:=hPre
 have hSubBound:∀V es,M2 mode es U V→∀r R,V.ND.state r=some R→ R.tree.vertices.card≤ size:=by
   intro V es hPass
   exact hBound V (preEdges++es) (hPrePass.Mh.append hPass)
 obtain ⟨j,T,es,D,hJ,hSmall,hCertified,hCover,hEncoding⟩:=Co A k hS hSubBound hOracle
   (execute pre G () ids data0) hPreEncoding target hTarget hB hOpt hClosed
 refine ⟨j,T,preEdges++es,D,hJ,hSmall,hPrePass.Mh.EX hCertified,?_,?_⟩
 · have hh:=hPrePass.Mh.Er.trans hCover hCertified.In
   simpa only [empty_union] using hh
 · change Fi T ids hi out hOut
     (execute (Mg pre (Mg (AD A k size ell mode j) (yE size ell mode))) G () ids data0)
   rw [AZ]
   exact hEncoding
end Fi
end Be
end
noncomputable section
namespace Be
structure wB {N ell: ℕ} {G M: SimpleGraph (Fin N)}
   (S: tI G M ell) (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (out: Fin N→ Option ℕ) (hOut: ReportsMatching G ids out M)
   (D: IO) (X: Finset (Fin N)) (hAuth: D.history.Li G ids out) where
 closed: D.history.JX
 view: tI D.history.graph D.history.MG ell
 valid: D.view ell=some view
 region: Bh (D.history.embedding hAuth hi hOut closed) view X S
namespace wB
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)} {S: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {D: IO} {X: Finset (Fin N)}
   {hAuth: D.history.Li G ids out}
   (A: wB S ids hi out hOut D X hAuth)
def embed:=D.history.embedding hAuth hi hOut A.closed
lemma Mz (a: Fin D.history.keys.card): ids (A.embed.toFun a)=D.history.identity a:=
 D.history.yA hAuth a
def FY (a: Fin D.history.keys.card): Option tF:=
 D.JD (D.history.oF hi hAuth) A.closed A.view.z9 a
lemma DU (a: Fin D.history.keys.card) (old: Ln) (hOld: old.Nm=false):
   D.Hf ell (D.history.identity a) old=
     {old with L8:=D.JD (D.history.oF hi hAuth) A.closed A.view.z9 a}:= by
 unfold IO.Hf
 rw [hOld]
 simp only [Bool.false_eq_true,if_false]
 rw [dif_pos (D.history.oF hi hAuth),dif_pos A.closed,A.valid]
 dsimp only
 have hExists:∃b,D.history.identity b=D.history.identity a:=⟨a,rfl⟩
 rw [dif_pos hExists]
 congr 2
 exact D.history.identity_injective hExists.choose_spec
end wB
namespace Fi
variable {N ell size: ℕ} {G M: SimpleGraph (Fin N)} {S: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (h: Fi S ids hi out hOut data)
   (hSize:∀r V,S.ND.state r=some V→ V.tree.vertices.card≤ size) (hS: 2≤ size)
include h in
lemma mP (v: Fin N):
   let P:=S.tT ids hi hSize hS
   Nonempty (wB S ids hi out hOut (P.NI ids data v) (P.block v)
     (IO.w7 _ h (IO.u2 (P.block v) ids data))):= by
 dsimp only
 let P:=S.tT ids hi hSize hS
 let D: IO:=P.NI ids data v
 have hAuth:∀z∈D,∃w,z=(ids w,data w):=IO.u2 (P.block v) ids data
 obtain ⟨hClosed,U,hU,hEmbed⟩:=D.ER S ids hi hSize hS
   (IO.AF P ids hi data v) out hOut data h hAuth
 have hRegion:=D.JP h hAuth hClosed U hU hEmbed
 have hSupport: D.Ig ids=P.block v:=IO.nF (P.block v) ids hi data
 rw [hSupport] at hRegion
 exact ⟨⟨hClosed,U,hU,hRegion⟩⟩
def FD (v: Fin N):=Classical.choice (h.mP hSize hS v)
end Fi
end Be
end
noncomputable section
namespace Be.Fi
variable {N ell size: ℕ} {G M: SimpleGraph (Fin N)} {S: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (h: Fi S ids hi out hOut data)
   (hSize:∀r V,S.ND.state r=some V→ V.tree.vertices.card≤ size) (hS: 2≤ size)
include h in
lemma kB (v: Fin N):
   let A:=h.FD hSize hS v
   G8.Mr A.embed A.view.z9.ND S.z9.ND:= by
 dsimp only
 apply (h.FD hSize hS v).region.frame.DV
 intro a ha b hb hLive
 let A:=h.FD hSize hS v
 have hAuth:∀z∈(S.tT ids hi hSize hS).NI ids data v,∃w,z=(ids w,data w):=
   IO.u2 ((S.tT ids hi hSize hS).block v) ids data
 rw [(IO.Lf _ ell A.view A.valid).NV]
 apply (IO.F6 _ h hAuth A.closed a b).mpr
 have hA: a∈IO.alive ((S.tT ids hi hSize hS).NI ids data v):=by
   have hr:=(IO.Lf _ ell A.view A.valid).Nm
   rw [hr] at ha
   simpa only [mem_sdiff,mem_univ,true_and,not_not] using ha
 have hB: b∈IO.alive ((S.tT ids hi hSize hS).NI ids data v):=by
   have hr:=(IO.Lf _ ell A.view A.valid).Nm
   rw [hr] at hb
   simpa only [mem_sdiff,mem_univ,true_and,not_not] using hb
 exact ⟨hA,hB,hLive⟩
end Be.Fi
end
noncomputable section
namespace Be.IO
lemma f1 (D: IO) (ell j: ℕ) (old: Ln) (hOld: old.Nm=true):
   D.Hf ell j old=old:= by simp only [Hf,hOld,if_true]
lemma qQ (D: IO) (ell j: ℕ) (old: Ln):
   ∃B,D.Hf ell j old={old with L8:=B}:= by
 unfold Hf
 by_cases hOld: old.Nm=true
 · rw [if_pos hOld]
   exact ⟨old.L8,rfl⟩
 · rw [if_neg hOld]
   by_cases hConsistent: D.history.JS
   · rw [dif_pos hConsistent]
     by_cases hClosed: D.history.JX
     · rw [dif_pos hClosed]
       cases hView: D.view ell with
       | none => exact ⟨old.L8,rfl⟩
       | some U =>
         dsimp only
         by_cases hIndex:∃a,D.history.identity a=j
         · rw [dif_pos hIndex]
           exact ⟨_,rfl⟩
         · rw [dif_neg hIndex]
           exact ⟨old.L8,rfl⟩
     · rw [dif_neg hClosed]
       exact ⟨old.L8,rfl⟩
   · rw [dif_neg hConsistent]
     exact ⟨old.L8,rfl⟩
end Be.IO
namespace Be.tE
variable {N size: ℕ} {G: SimpleGraph (Fin N)} (P: tE G size)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (data: Fin N→ Ln)
   (hTags:∀v,(data v).leader (ids v)=ids (P.leader v)) (ell: ℕ)
include hi hTags in
lemma d2 (v: Fin N):
   execute (rG size ell) G () ids data v=
     IO.Hf (P.NI ids data v) ell (ids v) (data v):= by
 unfold execute rG
 rw [C7.A4,C7.FS]
 have hInput:(fun w=>((data w).leader (ids w),data w))=(fun w=>(ids (P.leader w),data w)):=by
   funext w
   exact congrArg (fun j=>(j,data w)) (hTags w)
 rw [hInput,P.I0 ids hi data v]
 rfl
end Be.tE
end
noncomputable section
namespace Be.Fi
variable {N ell size: ℕ} {G M: SimpleGraph (Fin N)} {S: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (h: Fi S ids hi out hOut data)
   (hSize:∀r V,S.ND.state r=some V→ V.tree.vertices.card≤ size) (hS: 2≤ size)
include h in
lemma rI (v: Fin N) (a: Fin (IO.history ((S.tT ids hi hSize hS).NI ids data v)).keys.card)
   (ha:(h.FD hSize hS v).embed.toFun a=v) (hAlive: v∉S.Nm):
   execute (rG size ell) G () ids data v=
     {data v with L8:=(h.FD hSize hS v).FY a}:= by
 rw [(S.tT ids hi hSize hS).d2 ids hi data (h.Gr hSize hS) ell v]
 have hID:(IO.history ((S.tT ids hi hSize hS).NI ids data v)).identity a=ids v:=
   ((h.FD hSize hS v).Mz a).symm.trans (congrArg ids ha)
 rw [←hID]
 exact (h.FD hSize hS v).DU a (data v) (h.CY v hAlive)
include h hSize hS in
lemma rH (v: Fin N) (B: tF)
   (hB:(execute (rG size ell) G () ids data v).L8=some B):
   B.Represents S.z9 ids hi out hOut∧ ids v∈B.members:= by
 by_cases hRemoved: v∈S.Nm
 · rw [(S.tT ids hi hSize hS).d2 ids hi data (h.Gr hSize hS) ell v,
     IO.f1 _ ell _ _ ((h.Nm v).mpr hRemoved),h.vO v hRemoved] at hB
   cases hB
 · let A:=h.FD hSize hS v
   have hIn: v∈(S.tT ids hi hSize hS).block v:=mem_filter.mpr ⟨mem_univ _,rfl⟩
   obtain ⟨a,ha,hAV⟩:=A.region.IV v hIn hRemoved
   change A.embed.toFun a=v at hAV
   rw [h.rI hSize hS v a hAV hRemoved] at hB
   have hAuth:(IO.history ((S.tT ids hi hSize hS).NI ids data v)).Li G ids out:=
     IO.w7 _ h (IO.u2 ((S.tT ids hi hSize hS).block v) ids data)
   have hh:=IO.lI _
     ((IO.history ((S.tT ids hi hSize hS).NI ids data v)).oF hi hAuth)
     A.closed A.view.z9 S.z9 ids hi out hOut hAuth
     (h.kB hSize hS v) a B hB
   refine ⟨hh.1,?_⟩
   have hID:=A.Mz a
   rw [hAV] at hID
   rw [←hID] at hh
   exact hh.2
include h hSize hS in
lemma kM (r: Fin N) (V: Lp G M r)
   (hV: S.z9.ND.state r=some V):
   ∃B,∀v∈V.tree.vertices,(execute (rG size ell) G () ids data v).L8=some B:= by
 change (S.ND.state r).map (fun V=>V.z8 S.NV S.MF)=some V at hV
 obtain ⟨Vold,hOld,hOV⟩:=Option.map_eq_some_iff.mp hV
 let A:=h.FD hSize hS r
 have hIn: r∈(S.tT ids hi hSize hS).block r:=mem_filter.mpr ⟨mem_univ _,rfl⟩
 obtain ⟨a,Q,hQ,hAR⟩:=A.region.cover r hIn Vold hOld
 change A.embed.toFun a=r at hAR
 let Qnew:=Q.z8 A.view.NV A.view.MF
 have hNew: A.view.z9.ND.state a=some Qnew:=by
   change (A.view.ND.state a).map (fun V=>V.z8 A.view.NV A.view.MF)=some Qnew
   rw [hQ]
   rfl
 have hMap:=h.kB hSize hS r a Qnew hNew
 have hVertices:(Qnew.Nd A.embed).tree.vertices=V.tree.vertices:=by
   let read: Fin N→ Option (Finset (Fin N)):=fun r=>(S.z9.ND.state r).map (fun Z=>Z.tree.vertices)
   have hProj: read (A.embed.toFun a)=some (Qnew.Nd A.embed).tree.vertices:=
     congrArg (fun z=>z.map (fun Z=>Z.tree.vertices)) hMap
   have hNewPhys: S.z9.ND.state r=some V:=by
     change (S.ND.state r).map (fun V=>V.z8 S.NV S.MF)=some V
     rw [hOld]
     exact congrArg some hOV
   have hOther: read r=some V.tree.vertices:=congrArg (fun z=>z.map (fun Z=>Z.tree.vertices)) hNewPhys
   exact (Option.some.inj (hOther.symm.trans ((congrArg read hAR).symm.trans hProj))).symm
 let B: tF:=⟨(IO.history ((S.tT ids hi hSize hS).NI ids data r)),
   ((IO.history ((S.tT ids hi hSize hS).NI ids data r)).oF hi
     (IO.w7 _ h (IO.u2 ((S.tT ids hi hSize hS).block r) ids data))),
   A.closed,a,Qnew,A.view.z9.complete a Qnew hNew⟩
 refine ⟨B,?_⟩
 intro v hv
 have hOldV: v∈Vold.tree.vertices:=by rw [←hOV,Vold.fA] at hv;exact hv
 have hSame:(S.tT ids hi hSize hS).leader v=(S.tT ids hi hSize hS).leader r:=
   (S.iR ids hi hSize hS r Vold hOld v hOldV).trans
     (S.iR ids hi hSize hS r Vold hOld r Vold.tree.MU).symm
 have hPackets:=(S.tT ids hi hSize hS).L3 ids data v r hSame
 have hPre: v∈Qnew.tree.vertices.image A.embed.toFun:=by
   rw [←Qnew.Aj A.embed,hVertices]
   exact hv
 obtain ⟨b,hb,hBV⟩:=mem_image.mp hPre
 have hAlive: v∉S.Nm:=S.k7 r Vold hOld v hOldV
 rw [(S.tT ids hi hSize hS).d2 ids hi data (h.Gr hSize hS) ell v,hPackets]
 have hID:(IO.history ((S.tT ids hi hSize hS).NI ids data r)).identity b=ids v:=
   (A.Mz b).symm.trans (congrArg ids hBV)
 rw [←hID]
 exact (congrArg Ln.L8 (A.DU b (data v) (h.CY v hAlive))).trans
   (IO.sS _ _ A.closed A.view.z9 a b Qnew hNew hb)
include h hSize hS in
lemma i1: Fi S.z9 ids hi out hOut
   (execute (rG size ell) G () ids data):= by
 have hFields (v: Fin N):∃B,execute (rG size ell) G () ids data v={data v with L8:=B}:=by
   rw [(S.tT ids hi hSize hS).d2 ids hi data (h.Gr hSize hS) ell v]
   exact IO.qQ _ ell _ _
 have hNei (v):(execute (rG size ell) G () ids data v).neighbors=(data v).neighbors:=by
   obtain ⟨B,hB⟩:=hFields v;rw [hB]
 have hMate (v):(execute (rG size ell) G () ids data v).Jf=(data v).Jf:=by
   obtain ⟨B,hB⟩:=hFields v;rw [hB]
 have hLab (v):(execute (rG size ell) G () ids data v).labels=(data v).labels:=by
   obtain ⟨B,hB⟩:=hFields v;rw [hB]
 have hRem (v):(execute (rG size ell) G () ids data v).Nm=(data v).Nm:=by
   obtain ⟨B,hB⟩:=hFields v;rw [hB]
 have hIgn (v):(execute (rG size ell) G () ids data v).ignored=(data v).ignored:=by
   obtain ⟨B,hB⟩:=hFields v;rw [hB]
 have hSaved (v):(execute (rG size ell) G () ids data v).Md=(data v).Md:=by
   obtain ⟨B,hB⟩:=hFields v;rw [hB]
 refine ⟨fun v=>(hNei v).trans (h.neighbors v),fun v=>(hMate v).trans (h.Jf v),
   ?_,?_,?_,h.rH hSize hS,h.kM hSize hS,?_⟩
 · intro u v;rw [hLab];exact h.labels u v
 · intro v;rw [hRem];exact h.Nm v
 · intro u v;rw [hRem,hRem,hIgn,hIgn];exact h.NV u v
 · simp only [hRem,hMate,hSaved]
   exact h.output
end Be.Fi
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma y5.dK (O: J3 G) (h: y5 true O.edges S T)
   {r: Fin N} (A: Lp G M r) (hA: T.ND.state r= some A)
   (hmod: A.modified= false) (hheld: A.NU= false) (hextended: A.extended= false)
   (P Z: v9 G M r) (hactive: A.active= some P) (hext: P.M4 Z)
   (hbound: Z.length≤ ell)
   (hknown:∀i,i< 2*(Z.length-1)→(Z.vertex i,Z.vertex (i+1))∈ A.tree.NS)
   (hlive:∀i,i< Z.length→ T.NV.Adj (Z.vertex (2*i)) (Z.vertex (2*i+1))):
   ∀i,i< Z.length→ T.labels (Z.KA i)≤ i+1:= by
 intro i hi
 by_contra hn
 have hbad:∃j,j< Z.length∧ j+1< T.labels (Z.KA j):=⟨i,hi,by omega⟩
 obtain ⟨j,hj,R,hroot,hstem⟩:= a6 T A hA P Z hactive hext hheld hextended hbound hknown hlive hbad
 have hex:∃A,T.ND.state r= some A∧ A.modified= false:=⟨A,hA,hmod⟩
 rw [←hroot] at hex
 obtain ⟨B,hB,hBm⟩:= hex
 have hBR: B= R.state:= Option.some.inj (hB.symm.trans R.present)
 subst B
 exact h.Ax O R hBm
lemma y5.dP (limit: ℕ) (O: J3 G)
   (h: y5 true O.edges (S.IX limit) T)
   {r: Fin N} (A: Lp G M r) (hA: T.ND.state r= some A)
   (hmod: A.modified= false) (hheld: A.NU= false)
   (P Z: v9 G M r) (hactive: A.active= some P) (hext: P.M4 Z)
   (hbound: Z.length≤ ell)
   (hknown:∀i,i< 2*(Z.length-1)→(Z.vertex i,Z.vertex (i+1))∈ A.tree.NS)
   (hlive:∀i,i< Z.length→ T.NV.Adj (Z.vertex (2*i)) (Z.vertex (2*i+1))):
   ∀i,i< Z.length→ T.labels (Z.KA i)≤ i+1:=
 h.dK O A hA hmod hheld (h.fV limit A hA hmod)
   P Z hactive hext hbound hknown hlive
lemma y5.oJ (limit: ℕ) (O: J3 G)
   (h: y5 true O.edges (S.IX limit) T) (hInternal: S.zA)
   {r: Fin N} (A: Lp G M r) (hA: T.ND.state r= some A)
   (hmod: A.modified= false) (hheld: A.NU= false)
   (P: v9 G M r) (hactive: A.active= some P) (hp: 0< P.length)
   (b: Fin N ×Fin N) (hMb: M.Adj b.1 b.2)
   (hBridge: T.NV.Adj (P.vertex (2*P.length)) b.1)
   (hM:¬M.Adj (P.vertex (2*P.length)) b.1)
   (hBound: P.length+1≤ ell) (hHigh: P.length+1< T.labels b):
   A.tree.Reaches (P.KA (P.length-1)).swap:= by
 have hHit: b.1∈ P.support∨ b.2∈ P.support:= by
   by_contra hnot
   have hnot': b.1∉ P.support∧ b.2∉ P.support:= not_or.mp hnot
   let R: y7 T (P.vertex (2*P.length)) b.1:=
     { root:= r
       state:= A
       present:= hA
       J5:= P
       Lq:= hactive
       NX:= P
       DL:= P.Hs
       inside:= A.inside P hactive
       labelled:= T.labelled r A hA P hactive
       NC:= rfl
       MK:= hheld
       H9:= h.fV limit A hA hmod
       bound:= hBound
       NW:= b.2
       matched:= hMb
       Kq:= hnot'.1
       Kp:= hnot'.2
       My:= hHigh
       IY:= hBridge
       zV:= hM}
   exact h.Ax O R hmod
 obtain ⟨j,hj,hForward|hReverse⟩:= P.B6 T.MG b hMb hHit
 · have hl:=(T.labelled r A hA P hactive).2 j hj
   change T.labels (P.KA j)≤ j+1 at hl
   rw [hForward] at hl
   omega
 · have hLastHead:(P.KA (P.length-1)).2= P.vertex (2*P.length):= by
     change P.vertex (2*(P.length-1)+2)= P.vertex (2*P.length)
     congr 1;omega
   have hReverseHead:(P.KA j).2= b.1:= congrArg Prod.snd hReverse
   have hjlast: j≠ P.length-1:= by
     intro heq
     rw [heq,hLastHead] at hReverseHead
     exact hBridge.ne hReverseHead
   have hjshort: j+1< P.length:= by omega
   have hEdge: T.NV.Adj (P.KA (P.length-1)).2 (P.KA j).2:= by
     rw [hLastHead,hReverseHead];exact hBridge
   have hUnmatched:¬M.Adj (P.KA (P.length-1)).2 (P.KA j).2:= by
     rw [hLastHead,hReverseHead];exact hM
   have hCache:= h.n5 (tI.zA.IX S hInternal limit)
     A hA hmod P hactive (P.length-1) j (by omega) hj hEdge hUnmatched
   rw [hLastHead] at hCache
   have hEdgeG: G.Adj (P.vertex (2*P.length)) (P.vertex (2*j+2)):= by
     change G.Adj (P.vertex (2*P.length)) (P.KA j).2
     rw [hReverseHead];exact T.MF hBridge
   have hNo:¬M.Adj (P.vertex (2*P.length)) (P.vertex (2*j+2)):= by
     change ¬M.Adj (P.vertex (2*P.length)) (P.KA j).2
     rw [hReverseHead];exact hM
   exact A.tree.cI P (A.inside P hactive) j hjshort hEdgeG hNo hCache
lemma y5.cQ (limit: ℕ) (O: J3 G)
   (h: y5 true O.edges (S.IX limit) T)
   {r: Fin N} (A: Lp G M r) (hA: T.ND.state r= some A)
   (hmod: A.modified= false) (hheld: A.NU= false)
   (P: v9 G M r) (hactive: A.active= some P)
   (b: Fin N ×Fin N) (hMb: M.Adj b.1 b.2)
   (hBridge: T.NV.Adj (P.vertex (2*P.length)) b.1) (hM:¬M.Adj (P.vertex (2*P.length)) b.1)
   (hBound: P.length+1≤ ell) (hHigh: P.length+1< T.labels b):
   ∃j,j< P.length∧ P.KA j= b.swap:= by
 have hHit: b.1∈ P.support∨ b.2∈ P.support:= by
   by_contra hnot
   have hn: b.1∉ P.support∧ b.2∉ P.support:= not_or.mp hnot
   let R: y7 T (P.vertex (2*P.length)) b.1:=
     { root:= r
       state:= A
       present:= hA
       J5:= P
       Lq:= hactive
       NX:= P
       DL:= P.Hs
       inside:= A.inside P hactive
       labelled:= T.labelled r A hA P hactive
       NC:= rfl
       MK:= hheld
       H9:= h.fV limit A hA hmod
       bound:= hBound
       NW:= b.2
       matched:= hMb
       Kq:= hn.1
       Kp:= hn.2
       My:= hHigh
       IY:= hBridge
       zV:= hM}
   exact h.Ax O R hmod
 obtain ⟨j,hj,hFwd|hRev⟩:= P.B6 T.MG b hMb hHit
 · have hlabel:=(T.labelled r A hA P hactive).2 j hj
   change T.labels (P.KA j)≤ j+1 at hlabel
   rw [hFwd] at hlabel
   omega
 · exact ⟨j,hj,hRev⟩
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
def qG (limit: ℕ) (S T: tI G M ell): Prop:=
 ∃(extensionOrder checkOrder: J3 G) (U V: tI G M ell),
   y5 true extensionOrder.edges (S.IX limit) U∧
   y5 false checkOrder.edges ((U.rC limit).Dk) V∧
   T=V.z9
def jV (limit: ℕ) (S T: tI G M ell): Prop:=
 ∃(U: tI G M ell) (O: J3 G),
   qG limit S U∧ y5 false O.edges U T
lemma jV.boundary {S T: tI G M ell} (limit: ℕ)
   (h: jV limit S T):
   T.zA∧ T.ND.n8 T.NV:= by
 obtain ⟨U,O,⟨E,C,V,W,hV,hW,rfl⟩,hT⟩:=h
 exact ⟨hT.iL W.aX,hT.Dt O⟩
variable {S T: tI G M ell}
lemma qG.qP (limit: ℕ) (h: qG limit S T): T.ND.IS ⊆S.ND.IS:= by
 obtain ⟨O,K,U,V,hU,hV,rfl⟩:= h
 exact (Bf.includeEdges V).qP.trans
   (hV.qP.trans ((Bf.backtrack (U.rC limit)).qP.trans
     ((Bf.hold U limit).qP.trans (hU.qP.trans
       (Bf.begin S limit).qP))))
lemma qG.Ml (limit: ℕ) (h: qG limit S T): T.G1≤ S.G1:= by
 obtain ⟨O,K,U,V,hU,hV,rfl⟩:= h
 have hu:= hU.Ml
 rw [S.A9] at hu
 have hv:= hV.Ml
 have hb:=(U.rC limit).E7
 rw [U.iC] at hb
 rw [V.n7]
 omega
lemma qG.rank_mono (limit: ℕ) (h: qG limit S T): T.LN≤ S.LN:= by
 obtain ⟨O,K,U,V,hU,hV,rfl⟩:= h
 have hu:=(S.IX limit).rank_mono U hU.Jj
 have hv:=((U.rC limit).Dk).rank_mono V hV.Jj
 change U.LN≤ S.LN at hu
 change V.LN≤ U.LN at hv
 exact hv.trans hu
lemma jV.qP (limit: ℕ) (h: jV limit S T): T.ND.IS ⊆S.ND.IS:= by
 obtain ⟨U,O,hU,hT⟩:= h
 exact hT.qP.trans (hU.qP limit)
lemma jV.Ml (limit: ℕ) (h: jV limit S T): T.G1≤ S.G1:= by
 obtain ⟨U,O,hU,hT⟩:= h
 exact hT.Ml.trans (hU.Ml limit)
lemma jV.rank_mono (limit: ℕ) (h: jV limit S T): T.LN≤ S.LN:= by
 obtain ⟨U,O,hU,hT⟩:= h
 exact (U.rank_mono T hT.Jj).trans (hU.rank_mono limit)
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
def fZ (limit: ℕ) (U T: tI G M ell): Prop:=
 ∃(O: J3 G) (V: tI G M ell) (K: J3 G),
   y5 false O.edges ((U.rC limit).Dk) V∧
   y5 false K.edges V.z9 T
lemma fZ.MF {limit: ℕ} {U T: tI G M ell} (h: fZ limit U T): T.NV≤ U.NV:= by
 obtain ⟨O,V,K,hV,hT⟩:= h
 exact hT.MF.trans hV.MF
lemma fZ.Jj {limit: ℕ} {U T: tI G M ell} (h: fZ limit U T):
   ∀e,T.labels e≤ U.labels e:= by
 obtain ⟨O,V,K,hV,hT⟩:= h
 exact fun e=>(hT.Jj e).trans (hV.Jj e)
lemma fZ.In {limit: ℕ} {U T: tI G M ell} (h: fZ limit U T): U.Nm ⊆T.Nm:= by
 obtain ⟨O,V,K,hV,hT⟩:= h
 exact hV.In.trans hT.In
lemma fZ.lP {limit: ℕ} {U T: tI G M ell} (h: fZ limit U T)
   (e: Fin N ×Fin N) (halive: e.1∉ T.Nm) (hs: U.ND.IP e): T.ND.IP e:= by
 have hAliveU: e.1∉ U.Nm:= fun he=> halive (h.In he)
 obtain ⟨O,V,K,hV,hT⟩:= h
 have hAliveV: e.1∉ V.Nm:= fun he=> halive (hT.In he)
 have hHold:=(Bf.hold U limit).lP e hAliveU hs
 have hBack:=(Bf.backtrack (U.rC limit)).lP e hAliveU hHold
 have hVV:= hV.lP e hAliveV hBack
 have hInc:=(Bf.includeEdges V).lP e hAliveV hVV
 exact hT.lP e halive hInc
def iD (limit: ℕ) (S T: tI G M ell)
   (e: Fin N ×Fin N) (k: ℕ) (E: Finset (Fin N ×Fin N)): Prop:=
 ∃(O: J3 G) (U: tI G M ell) (r: Fin N) (R: Lp G M r),
   y5 true O.edges (S.IX limit) U∧
   (U.rC limit).ND.state r= some R∧ R.II e k E∧
   fZ limit U T
lemma jV.CT {S T: tI G M ell} (limit: ℕ)
   (h: jV limit S T) (a: ℕ→ Fin N ×Fin N) (n k: ℕ) (hn: 0< n)
   (E: Finset (Fin N ×Fin N)) (hE:∀e∈ E,∃i,i< n∧(e= a i∨ e=(a i).swap))
   (hmatched:∀i,i< n→ M.Adj (a i).1 (a i).2)
   (hUnmatched:∀i,i+1< n→¬M.Adj (a i).2 (a (i+1)).1)
   (halive:∀i,i< n→(a i).1∉ T.Nm) (hs: S.ND.G4 a n k E):
   T.ND.G4 a n k E∨ iD limit S T (a 0) k E:= by
 obtain ⟨B,Oextra,hBase,hExtra⟩:= h
 obtain ⟨Oext,Ocheck,U,V,hExt,hCheck,rfl⟩:= hBase
 let H:= U.rC limit
 have hURem: U.Nm ⊆T.Nm:=
   (show U.Nm ⊆V.Nm from hCheck.In).trans hExtra.In
 have hAliveU:∀i,i< n→(a i).1∉ U.Nm:= fun i hi he=> halive i hi (hURem he)
 have hExtTrack:= hExt.Ds a n k hn E hE hmatched hUnmatched hAliveU (S.IZ a n k E limit hs)
 have hHold:= U.Ka a n k E limit hExtTrack
 obtain ⟨r,R,hR,hRootTrack⟩:= hHold.1
 rcases R.h8 (a 0) k E hRootTrack with hBackTrack|hLeaf
 · left
   have hBack: H.Dk.ND.G4 a n k E:= by
     constructor
     · refine ⟨r,R.zS,?_,hBackTrack⟩
       change (H.ND.state r).map (fun R=> R.zS)= some R.zS
       rw [hR];rfl
     · intro i hi
       apply H.ND.Hw (fun _ R=> R.tree.Mo (a i) (a (i+1)).swap)
         (fun _ R=> R.zS) _ _ (hHold.2 i hi)
       · intro r R;unfold Lp.zS;split_ifs<;> rfl
       · intro r R hp;unfold Lp.zS;split_ifs<;> exact hp
   have hAliveV:∀i,i< n→(a i).1∉ V.Nm:= fun i hi he=> halive i hi (hExtra.In he)
   have hV:= hCheck.Ds a n k hn E hE hmatched hUnmatched hAliveV hBack
   exact hExtra.Ds a n k hn E hE hmatched hUnmatched halive (V.FA a n k E hV)
 · right
   exact ⟨Oext,U,r,R,hExt,hR,hLeaf,Ocheck,V,Oextra,hCheck,hExtra⟩
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma iD.tR (limit: ℕ) (C: C9 G M) (hC: 1< C.length)
   (k: ℕ) (E: Finset (Fin N ×Fin N)) (h: iD limit S T (C.KA 0) k E)
   (hInternal: S.zA)
   (hLinks:∀j,j+1< C.length→ S.ND.JV (C.KA j) (C.KA (j+1)).swap)
   (hAvoided:∀j,0< j→ j< C.length→ C.KA j∈ E∧(C.KA j).swap∈ E)
   (hLive:∀j,j< 2*C.length-1→ T.NV.Adj (C.vertex j) (C.vertex (j+1)))
   (hBound: k+C.length≤ ell): T.labels (C.KA (C.length-1))≤ k+C.length:= by
 obtain ⟨O,U,r,R,hPass,hPresent,hBack,hSuffix⟩:= h
 change (U.ND.state r).map (fun R=> R.rC limit)= some R at hPresent
 obtain ⟨A,hA,hAR⟩:= Option.map_eq_some_iff.mp hPresent
 rw [←hAR] at hBack
 obtain ⟨P,i,hP,hi,hik,hie,havoid,hleaf,hHeld,hMod⟩:= hBack
 change A.active= some P at hP
 change A.modified= false at hMod
 change (A.NU|| decide (limit≤ A.tree.vertices.card))= false at hHeld
 have hAheld: A.NU= false:= by cases hh: A.NU<;> simp_all
 have hUnmatched (j: ℕ) (hj: j+1< C.length):¬M.Adj (C.KA j).2 (C.KA (j+1)).1:= by
   intro hm
   have hm': M.Adj (C.vertex (2*j+1)) (C.vertex (2*j+2)):= by
     convert hm using 1<;> congr 1<;> omega
   have heven:=(C.MG (2*j+1) (by omega)).mp hm'
   obtain ⟨v,hv⟩:= heven
   omega
 have hAliveT (j: ℕ) (hj: j< C.length):(C.KA j).1∉ T.Nm:=
   (T.HK _ _ (hLive (2*j) (by omega))).1
 have hAliveU (j: ℕ) (hj: j< C.length):(C.KA j).1∉ U.Nm:=
   fun he=> hAliveT j hj (hSuffix.In he)
 have hLinksU:∀j,j+1< C.length→ U.ND.JV (C.KA j) (C.KA (j+1)).swap:= by
   intro j hj
   have hAliveS:(C.KA j).1∉ S.Nm:= fun he=> hAliveU j (by omega) (hPass.In he)
   have hBegin:=(Bf.begin S limit).q9 (C.KA j) (C.KA (j+1)).swap
     (hUnmatched j hj) hAliveS (hLinks j hj)
   exact hPass.q9 (C.KA j) (C.KA (j+1)).swap (hUnmatched j hj) (hAliveU j (by omega)) hBegin
 have hTrack: A.Ny (C.KA 0) k E:=⟨P,i,hP,hi,hik,hie,havoid⟩
 have hCSupport:= U.ND.e5 U.MG C hLinksU A hA (A.CU hTrack)
 let Q:= C.LB hC
 have hDisjoint: Disjoint P.support Q.support:= by
   apply P.bL Q U.MG E i hleaf havoid
   intro j hj
   change (C.LB hC).KA j∈ E∧((C.LB hC).KA j).swap∈ E
   rw [C.FH]
   exact hAvoided (j+1) (by omega) (by change j<C.length-1 at hj;omega)
 have hPHead: P.vertex (2*P.length)= C.vertex 1:= by
   have hh:= congrArg Prod.snd hie
   change P.vertex (2*i+2)= C.vertex (2*0+1) at hh
   have hh': 2*i+2= 2*P.length:= by omega
   simpa only [hh',Nat.mul_zero,Nat.zero_add] using hh
 have hBridge: U.NV.Adj (P.vertex (2*P.length)) (Q.vertex 0):= by
   rw [hPHead]
   change U.NV.Adj (C.vertex 1) (C.vertex 2)
   exact hSuffix.MF (hLive 1 (by omega))
 have hM:¬M.Adj (P.vertex (2*P.length)) (Q.vertex 0):= by
   rw [hPHead]
   change ¬M.Adj (C.vertex 1) (C.vertex 2)
   simpa only [C9.KA,Nat.mul_zero,Nat.zero_add,Nat.zero_add,Nat.mul_one] using hUnmatched 0 hC
 have hPLive:∀j,j< 2*P.length→ U.NV.Adj (P.vertex j) (P.vertex (j+1)):=
   fun j hj=> U.I9 r A hA _ _ (A.inside P hP j hj)
 have hQLive:∀j,j< 2*Q.length-1→ U.NV.Adj (Q.vertex j) (Q.vertex (j+1)):= by
   intro j hj
   change U.NV.Adj (C.vertex (j+2)) (C.vertex (j+1+2))
   have he:= hSuffix.MF (hLive (j+2) (by change j<2*(C.length-1)-1 at hj;omega))
   convert he using 1<;> congr 1<;> omega
 let Z:= P.Fr Q hDisjoint (U.MF hBridge) hM
 let P':= P.Nq U.NV hPLive
 let Q':= Q.Nq U.NV hQLive
 let Z':= P'.Fr Q' hDisjoint hBridge hM
 have hZLive:∀j,j< 2*Z.length→ U.NV.Adj (Z.vertex j) (Z.vertex (j+1)):= Z'.Mu
 have hZVertices: Z.support ⊆A.tree.vertices:=
   (P.l5 Q hDisjoint (U.MF hBridge) hM).trans
     (union_subset (A.tree.EA P (A.inside P hP)) ((C.wW hC).trans hCSupport))
 have hZInside:= hPass.h9 (tI.zA.IX S hInternal limit)
   A hA hMod Z hZVertices hZLive
 have hZBound: Z.length≤ ell:= by change P.length+(C.length-1)≤ell;omega
 have hLabels:= hPass.dP limit O A hA hMod hAheld P Z hP
   (P.l4 Q hDisjoint (U.MF hBridge) hM) hZBound
   (fun j hj=> hZInside j (by omega)) (fun j hj=> hZLive (2*j) (by omega))
 have hZPos: 0< Z.length:= by change 0<P.length+(C.length-1);omega
 have hLast:= hLabels (Z.length-1) (by omega)
 have hLastArc: Z.KA (Z.length-1)= C.KA (C.length-1):=
   (P.tN Q hDisjoint (U.MF hBridge) hM).trans (C.DA hC)
 rw [hLastArc] at hLast
 have hLastBound: Z.length-1+1≤ k+C.length:= by change P.length+(C.length-1)-1+1≤k+C.length;omega
 exact (hSuffix.Jj _).trans (hLast.trans hLastBound)
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma jV.In (limit: ℕ) (h: jV limit S T): S.Nm ⊆T.Nm:= by
 obtain ⟨B,K,hBase,hExtra⟩:= h
 obtain ⟨O,J,U,V,hExt,hCheck,rfl⟩:= hBase
 exact hExt.In.trans (hCheck.In.trans hExtra.In)
lemma jV.MF (limit: ℕ) (h: jV limit S T): T.NV≤ S.NV:= by
 obtain ⟨B,K,hBase,hExtra⟩:= h
 obtain ⟨O,J,U,V,hExt,hCheck,rfl⟩:= hBase
 exact hExtra.MF.trans (hCheck.MF.trans hExt.MF)
lemma jV.Jj (limit: ℕ) (h: jV limit S T):∀e,T.labels e≤ S.labels e:= by
 obtain ⟨B,K,hBase,hExtra⟩:= h
 obtain ⟨O,J,U,V,hExt,hCheck,rfl⟩:= hBase
 exact fun e=>(hExtra.Jj e).trans ((hCheck.Jj e).trans (hExt.Jj e))
lemma jV.lP (limit: ℕ) (h: jV limit S T)
   (e: Fin N ×Fin N) (halive: e.1∉ T.Nm) (hs: S.ND.IP e): T.ND.IP e:= by
 have hAliveS: e.1∉ S.Nm:= fun he=> halive (h.In limit he)
 obtain ⟨B,K,hBase,hExtra⟩:= h
 obtain ⟨O,J,U,V,hExt,hCheck,rfl⟩:= hBase
 have hSuffix: fZ limit U T:=⟨J,V,K,hCheck,hExtra⟩
 have hAliveU: e.1∉ U.Nm:= fun he=> halive (hSuffix.In he)
 have hBegin:=(Bf.begin S limit).lP e hAliveS hs
 exact hSuffix.lP e halive (hExt.lP e hAliveU hBegin)
lemma bD (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1)))
   (e: Fin N ×Fin N) (hzero:(states 0).ND.IP e) (T: ℕ)
   (halive: e.1∉(states T).Nm):(states T).ND.IP e:= by
 induction T with
 | zero => exact hzero
 | succ T ih =>
   have haliveT: e.1∉(states T).Nm:= fun he=> halive ((hstep T).In limit he)
   exact (hstep T).lP limit e halive (ih haliveT)
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma jV.f7 (limit: ℕ) (h: jV limit S T)
   (C: C9 G M) (hC: 1< C.length) (k: ℕ) (hInternal: S.zA)
   (hs: S.ND.G4 C.KA C.length k C.z5)
   (hLive:∀i,i< 2*C.length-1→ T.NV.Adj (C.vertex i) (C.vertex (i+1)))
   (hBound: k+C.length≤ ell) (hHigh: k+C.length< T.labels (C.KA (C.length-1))):
   T.ND.G4 C.KA C.length k C.z5:= by
 have hE:∀e∈ C.z5,∃i,i< C.length∧(e= C.KA i∨ e=(C.KA i).swap):= by
   intro e he
   obtain ⟨i,hi0,hi,heq⟩:= C.kG e he
   exact ⟨i,hi,heq⟩
 have hAlive:∀i,i< C.length→(C.KA i).1∉ T.Nm:= by
   intro i hi
   exact (T.HK _ _ (hLive (2*i) (by omega))).1
 rcases h.CT limit C.KA C.length k C.positive C.z5 hE
   (fun i hi=> C.HR i hi) (fun i hi=> C.s4 i hi) hAlive hs with hnew|hframe
 · exact hnew
 · have hlabel:= hframe.tR limit C hC k C.z5 hInternal hs.2 C.e4 hLive hBound
   omega
lemma aG (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1))) (hInternal:∀t,(states t).zA)
   (C: C9 G M) (hC: 1< C.length) (k: ℕ)
   (hStart:(states 0).ND.G4 C.KA C.length k C.z5)
   (hBound: k+C.length≤ ell) (T: ℕ)
   (hLive:∀i,i< 2*C.length-1→(states T).NV.Adj (C.vertex i) (C.vertex (i+1)))
   (hHigh: k+C.length<(states T).labels (C.KA (C.length-1))):
   (states T).ND.G4 C.KA C.length k C.z5:= by
 induction T with
 | zero => exact hStart
 | succ T ih =>
   have hLiveT:∀i,i< 2*C.length-1→(states T).NV.Adj (C.vertex i) (C.vertex (i+1)):=
     fun i hi=>(hstep T).MF limit (hLive i hi)
   have hHighT: k+C.length<(states T).labels (C.KA (C.length-1)):=
     hHigh.trans_le ((hstep T).Jj limit _)
   exact (hstep T).f7 limit C hC k (hInternal T) (ih hLiveT hHighT) hLive hBound hHigh
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma fZ.LO {limit: ℕ} {U T: tI G M ell} (h: fZ limit U T): T.labels= U.labels:= by
 obtain ⟨O,V,K,hV,hT⟩:= h
 exact hT.Bv.trans hV.Bv
lemma fZ.vK {limit: ℕ} {U T: tI G M ell} (h: fZ limit U T)
   (e: Fin N ×Fin N) (k: ℕ) (halive: e.1∉ T.Nm) (hs: U.ND.Bg e k):
   T.ND.Bg e k:= by
 obtain ⟨O,V,K,hV,hT⟩:= h
 have hAliveV: e.1∉ V.Nm:= fun he=> halive (hT.In he)
 have hHold:= U.ED e k limit hs
 have hBack:=(U.rC limit).sJ e k hHold
 have hVV:= hV.vK e k hAliveV hBack
 exact hT.vK e k halive (V.yD e k hVV)
lemma jV.o6 (limit: ℕ) (h: jV limit S T)
   (e: Fin N ×Fin N) (halive: e.1∉ T.Nm) (hdrop: T.labels e< S.labels e):
   T.ND.Bg e (T.labels e-1):= by
 obtain ⟨B,K,hBase,hExtra⟩:= h
 obtain ⟨O,J,U,V,hExt,hCheck,rfl⟩:= hBase
 have hSuffix: fZ limit U T:=⟨J,V,K,hCheck,hExtra⟩
 have hAliveU: e.1∉ U.Nm:= fun he=> halive (hSuffix.In he)
 have hStrict: U.labels e<(S.IX limit).labels e:= by rw [←hSuffix.LO];exact hdrop
 have hProtected:= hExt.o6 e hAliveU hStrict
 have hFinal:= hSuffix.vK e (U.labels e-1) halive hProtected
 rwa [←hSuffix.LO] at hFinal
lemma bB (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1)))
   (hzero:∀e,(states 0).labels e= ell+1) (T: ℕ) (e: Fin N ×Fin N)
   (ha:(states T).labels e≤ ell) (halive: e.1∉(states T).Nm):
   ∃t,t< T∧(states (t+1)).ND.Bg e ((states T).labels e-1):= by
 induction T with
 | zero => rw [hzero] at ha;omega
 | succ T ih =>
   have hm:=(hstep T).Jj limit e
   by_cases heq:(states (T+1)).labels e=(states T).labels e
   · have hAliveT: e.1∉(states T).Nm:= fun he=> halive ((hstep T).In limit he)
     obtain ⟨t,ht,htrack⟩:= ih (by omega) hAliveT
     exact ⟨t,by omega,by rwa [heq]⟩
   · have hdrop:(states (T+1)).labels e<(states T).labels e:= by omega
     exact ⟨T,by omega,(hstep T).o6 limit e halive hdrop⟩
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma aE (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1)))
   (hzero:(states 0).zA):∀t,(states t).zA:= by
 intro t
 cases t with
 | zero => exact hzero
 | succ t => exact ((hstep t).boundary limit).1
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma fZ.yF {limit: ℕ} {U T: tI G M ell} (h: fZ limit U T)
   (e: Fin N ×Fin N) (halive: e.1∉ T.Nm) (hs: U.ND.M7 e): T.ND.M7 e:= by
 have hAliveU: e.1∉ U.Nm:= fun he=> halive (h.In he)
 obtain ⟨O,V,K,hV,hT⟩:= h
 have hAliveV: e.1∉ V.Nm:= fun he=> halive (hT.In he)
 have hHold:=(Bf.hold U limit).yF e hAliveU hs
 have hBack:=(Bf.backtrack (U.rC limit)).yF e hAliveU hHold
 have hVV:= hV.yF e hAliveV hBack
 have hInc:=(Bf.includeEdges V).yF e hAliveV hVV
 exact hT.yF e halive hInc
lemma jV.yF (limit: ℕ) (h: jV limit S T)
   (e: Fin N ×Fin N) (halive: e.1∉ T.Nm) (hs: S.ND.M7 e): T.ND.M7 e:= by
 have hAliveS: e.1∉ S.Nm:= fun he=> halive (h.In limit he)
 obtain ⟨B,K,hBase,hExtra⟩:= h
 obtain ⟨O,J,U,V,hExt,hCheck,rfl⟩:= hBase
 have hSuffix: fZ limit U T:=⟨J,V,K,hCheck,hExtra⟩
 have hAliveU: e.1∉ U.Nm:= fun he=> halive (hSuffix.In he)
 have hBegin:=(Bf.begin S limit).yF e hAliveS hs
 exact hSuffix.yF e halive (hExt.yF e hAliveU hBegin)
lemma bC (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1)))
   (e: Fin N ×Fin N) (hzero:(states 0).ND.M7 e) (T: ℕ)
   (halive: e.1∉(states T).Nm):(states T).ND.M7 e:= by
 induction T with
 | zero => exact hzero
 | succ T ih =>
   have hAliveT: e.1∉(states T).Nm:= fun he=> halive ((hstep T).In limit he)
   exact (hstep T).yF limit e halive (ih hAliveT)
lemma bM (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1)))
   (hzero:∀e,(states 0).labels e= ell+1) (T: ℕ) (e: Fin N ×Fin N)
   (ha:(states T).labels e≤ ell) (halive: e.1∉(states T).Nm):(states T).ND.M7 e:= by
 obtain ⟨t,ht,r,R,hR,hm,P,i,hP,hi,hik,hie,havoid⟩:= bB states limit hstep hzero T e ha halive
 have hReaches:= R.tL P hP i hi
 rw [hie] at hReaches
 let shifted (u: ℕ):= states (t+1+u)
 have hShift:∀u,jV limit (shifted u) (shifted (u+1)):= by
   intro u
   simpa only [shifted,Nat.add_assoc] using hstep (t+1+u)
 let L:= T-(t+1)
 have hEnd: shifted L= states T:= by dsimp only [shifted,L];congr 1;omega
 have hStart:(shifted 0).ND.M7 e:=⟨r,R,hR,hReaches⟩
 have hAliveEnd: e.1∉(shifted L).Nm:= by rw [hEnd];exact halive
 have hResult:= bC shifted limit hShift e hStart L hAliveEnd
 rwa [hEnd] at hResult
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma aB (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1))) (hInternal:∀t,(states t).zA)
   (C: C9 G M) (hC: 1< C.length) (k: ℕ)
   (hLinks:∀j,j+1< C.length→(states 0).ND.JV (C.KA j) (C.KA (j+1)).swap)
   (hReverse:∀j,0< j→ j< C.length→(states 0).ND.M7 (C.KA j).swap)
   {r: Fin N} (A: Lp G M r) (hA:(states 0).ND.state r= some A)
   (P: v9 G M r) (hactive: A.active= some P) (i: ℕ) (hi: i< P.length)
   (hik: i≤ k) (hFirst: P.KA i= C.KA 0)
   (hBound: k+C.length≤ ell) (T: ℕ)
   (hLive:∀j,j< 2*C.length-1→(states T).NV.Adj (C.vertex j) (C.vertex (j+1)))
   (hHigh: k+C.length<(states T).labels (C.KA (C.length-1)))
   (hInactive:¬(states T).ND.Lh (C.KA 0)):
   (states 0).ND.IP (C.KA 0):= by
 have hForwardA: A.tree.Reaches (C.KA 0):= by
   have h:= A.tL P hactive i hi
   rwa [hFirst] at h
 by_contra hNotSettled
 have hNoReverse:¬A.tree.Reaches (C.KA 0).swap:= by
   intro hRev
   exact hNotSettled ⟨r,A,hA,hForwardA,hRev⟩
 have hSupport:=(states 0).ND.e5 (states 0).MG C hLinks A hA
   (A.tree.yG _ hForwardA).1
 have hAnti: Antitone (fun t=>(states t).NV):= antitone_nat_of_succ_le (fun t=>(hstep t).MF limit)
 have hLive0:∀j,j< 2*C.length-1→(states 0).NV.Adj (C.vertex j) (C.vertex (j+1)):=
   fun j hj=>(hAnti (Nat.zero_le T)) (hLive j hj)
 let D:= C.Nq (Mv G A.tree.NS) (fun j hj=>
   (states 0).o3 (hInternal 0) A hA _ _ (hLive0 j hj)
     (hSupport (C.mem_support j (by omega))) (hSupport (C.mem_support (j+1) (by omega))))
 have hReverseA:∀j,0< j→ j< D.length→ Fk (Mv G A.tree.NS) M r (D.KA j).swap:= by
   intro j hj0 hj
   exact (states 0).ND.AJ (C.KA j).swap A hA
     (hSupport (C.mem_support (2*j+1) (by change j<C.length at hj;omega))) (hReverse j hj0 hj)
 let Q:= P.Kt A.tree.NS (A.inside P hactive)
 have hAvoid:= D.eR (states 0).MG hNoReverse hReverseA Q i hi hFirst
 have hTrack: A.Ny (C.KA 0) k C.z5:=⟨P,i,hactive,hi,hik,hFirst,hAvoid⟩
 have hStart:(states 0).ND.G4 C.KA C.length k C.z5:=⟨⟨r,A,hA,hTrack⟩,hLinks⟩
 have hEnd:= aG states limit hstep hInternal C hC k hStart hBound T hLive hHigh
 obtain ⟨s,B,hB,hBtrack⟩:= hEnd.1
 exact hInactive ⟨k,s,B,hB,B.IF _ k _ hBtrack⟩
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma aA (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1))) (hInternal:∀t,(states t).zA)
   (hJump:(states 0).ND.M5 (states 0).labels)
   (C: C9 G M) (hC: 1< C.length) (k: ℕ)
   (hLinks:∀j,j+1< C.length→(states 0).ND.JV (C.KA j) (C.KA (j+1)).swap)
   (hForward:(states 0).ND.M7 (C.KA 0))
   (hReverse:∀j,0< j→ j< C.length→(states 0).ND.M7 (C.KA j).swap)
   (hLabel:(states 0).labels (C.KA 0)≤ k+1)
   (hActive:(states 0).ND.Lh (C.KA 0)∨(states 0).ND.Lh (C.KA 0).swap)
   (hBound: k+C.length≤ ell) (T: ℕ)
   (hLive:∀j,j< 2*C.length-1→(states T).NV.Adj (C.vertex j) (C.vertex (j+1)))
   (hHigh: k+C.length<(states T).labels (C.KA (C.length-1)))
   (hInactive:¬(states T).ND.Lh (C.KA 0)):
   (states 0).ND.IP (C.KA 0):= by
 rcases hActive with hActive|hReverseActive
 · obtain ⟨bound,r,A,hA,P,i,hP,hi,hib,hie,havoid⟩:= hActive
   by_cases hik: i≤ k
   · exact aB states limit hstep hInternal C hC k hLinks hReverse
       A hA P hP i hi hik hie hBound T hLive hHigh hInactive
   · have hstrict:(states 0).labels (P.KA i)< i+1:= by rw [hie];omega
     have hRev:= hJump r A hA P hP i hi hstrict
     rw [hie] at hRev
     have hFwd:= A.tL P hP i hi
     rw [hie] at hFwd
     exact ⟨r,A,hA,hFwd,hRev⟩
 · obtain ⟨bound,r,A,hA,htrack⟩:= hReverseActive
   have hr:= A.E0 (C.KA 0).swap bound ∅ htrack
   exact (states 0).ND.lO (C.KA 0) hForward ⟨r,A,hA,hr⟩
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma iD.AT (limit: ℕ) (e: Fin N ×Fin N) (k: ℕ)
   (E: Finset (Fin N ×Fin N)) (h: iD limit S T e k E)
   (hInternal: S.zA) (b: Fin N ×Fin N) (hMb: M.Adj b.1 b.2)
   (hBridge: T.NV.Adj e.2 b.1) (hM:¬M.Adj e.2 b.1)
   (hBound: k+2≤ ell) (hHigh: k+2< T.labels b):
   S.ND.IP e∧ S.ND.Lh b.swap:= by
 obtain ⟨O,U,r,R,hPass,hPresent,hBack,hSuffix⟩:= h
 change (U.ND.state r).map (fun R=> R.rC limit)= some R at hPresent
 obtain ⟨A,hA,hAR⟩:= Option.map_eq_some_iff.mp hPresent
 rw [←hAR] at hBack
 obtain ⟨P,i,hP,hi,hik,hie,havoid,hleaf,hHeld,hMod⟩:= hBack
 change A.active= some P at hP
 change A.modified= false at hMod
 change (A.NU|| decide (limit≤ A.tree.vertices.card))= false at hHeld
 have hAheld: A.NU= false:= by cases hh: A.NU<;> simp_all
 have hp: 0< P.length:= by omega
 have hLast: P.KA (P.length-1)= e:= by rw [show P.length-1=i by omega];exact hie
 have hHead: P.vertex (2*P.length)= e.2:= by
   have hh:= congrArg Prod.snd hLast
   change P.vertex (2*(P.length-1)+2)= e.2 at hh
   rwa [show 2*(P.length-1)+2=2*P.length by omega] at hh
 have hBridgeU: U.NV.Adj (P.vertex (2*P.length)) b.1:= by rw [hHead];exact hSuffix.MF hBridge
 have hMU:¬M.Adj (P.vertex (2*P.length)) b.1:= by rw [hHead];exact hM
 have hBoundP: P.length+1≤ ell:= by omega
 have hHighU: P.length+1< U.labels b:= by have hm:=hSuffix.Jj b;omega
 have hRevU:= hPass.oJ limit O hInternal A hA hMod hAheld P hP hp b hMb hBridgeU hMU hBoundP hHighU
 rw [hLast] at hRevU
 obtain ⟨j,hj,hReverseTarget⟩:= hPass.cQ limit O A hA hMod hAheld P hP b hMb hBridgeU hMU hBoundP hHighU
 obtain ⟨B,hB,hBm,hVertices,hGraph,hCache⟩:= hPass.lY r A hA hMod
 obtain ⟨D,hD,hDm,hActive,hHeldB,hExtendedB⟩:= hPass.CX r A hA hMod
 have hBD: B= D:= Option.some.inj (hB.symm.trans hD)
 subst D
 have hBP: B.active= some P:= hActive.symm.trans hP
 have hRevB:= A.tree.vM B.tree hGraph e.swap hRevU
 change (S.ND.state r).map (fun R=> R.IX limit)= some B at hB
 obtain ⟨C,hC,hCB⟩:= Option.map_eq_some_iff.mp hB
 rw [←hCB] at hBP hRevB
 have hCP: C.active= some P:= hBP
 have hForwardC:= C.tL P hCP (P.length-1) (by omega)
 rw [hLast] at hForwardC
 exact ⟨⟨r,C,hC,hForwardC,hRevB⟩,S.ND.tK C hC P hCP j hj b.swap hReverseTarget⟩
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma b8 (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1)))
   (e: Fin N ×Fin N) (k: ℕ) (hstart:(states 0).ND.Ny e k ∅) (T: ℕ)
   (halive: e.1∉(states T).Nm) (hlost:¬(states T).ND.Ny e k ∅):
   ∃t,t< T∧ iD limit (states t) (states (t+1)) e k ∅:= by
 induction T with
 | zero => exact (hlost hstart).elim
 | succ T ih =>
   by_cases hprev:(states T).ND.Ny e k ∅
   · let a: ℕ→ Fin N ×Fin N:= fun _=> e
     have hMe: M.Adj e.1 e.2:= by
       obtain ⟨r,R,hR,htrack⟩:= hprev
       exact R.EZ e k ∅ htrack
     have hchain:(states T).ND.G4 a 1 k ∅:=⟨hprev,by intro i hi;omega⟩
     have hE:∀f∈(∅:Finset (Fin N ×Fin N)),∃i,i< 1∧(f= a i∨ f=(a i).swap):= by simp
     have hmatch:∀i,i< 1→ M.Adj (a i).1 (a i).2:= fun _ _=> hMe
     have hun:∀i,i+1< 1→¬M.Adj (a i).2 (a (i+1)).1:= by intro i hi;omega
     have hal:∀i,i< 1→(a i).1∉(states (T+1)).Nm:= fun _ _=> halive
     rcases (hstep T).CT limit a 1 k (by omega) ∅ hE hmatch hun hal hchain with hnew|hframe
     · exact (hlost hnew.1).elim
     · exact ⟨T,by omega,hframe⟩
   · have hAliveT: e.1∉(states T).Nm:= fun he=> halive ((hstep T).In limit he)
     obtain ⟨t,ht,hframe⟩:= ih hAliveT hprev
     exact ⟨t,by omega,hframe⟩
lemma aF (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1)))
   (hInternal:∀t,(states t).zA) (hzero:∀e,(states 0).labels e= ell+1)
   (T: ℕ) (e b: Fin N ×Fin N) (k: ℕ)
   (hLabel:(states T).labels e≤ k+1) (hInactive:¬(states T).ND.Lh e)
   (hMb: M.Adj b.1 b.2) (hM:¬M.Adj e.2 b.1) (hBound: k+2≤ ell)
   (halive: e.1∉(states T).Nm) (hBridge:(states T).NV.Adj e.2 b.1)
   (hHigh: k+2<(states T).labels b):
   ∃t,0< t∧ t< T∧(states t).ND.IP e∧(states t).ND.Lh b.swap:= by
 have hfinite:(states T).labels e≤ ell:= by omega
 obtain ⟨t,ht,r,R,hR,hm,htrack⟩:= bB states limit hstep hzero T e hfinite halive
 have hStart:(states (t+1)).ND.Ny e k ∅:=⟨r,R,hR,R.y0 e (by omega) ∅ htrack⟩
 let shifted (u: ℕ):= states (t+1+u)
 have hShiftStep:∀u,jV limit (shifted u) (shifted (u+1)):= by
   intro u
   simpa only [shifted,Nat.add_assoc] using hstep (t+1+u)
 let L:= T-(t+1)
 have hEnd: shifted L= states T:= by dsimp only [shifted,L];congr 1;omega
 have hAliveEnd: e.1∉(shifted L).Nm:= by rw [hEnd];exact halive
 have hLostEnd:¬(shifted L).ND.Ny e k ∅:= by
   rw [hEnd]
   exact fun h=> hInactive ⟨k,h⟩
 obtain ⟨u,hu,hframe⟩:= b8 shifted limit hShiftStep e k hStart L hAliveEnd hLostEnd
 have hBefore: t+1+(u+1)≤ T:= by dsimp [L] at hu;omega
 have hAntiLive: Antitone (fun t=>(states t).NV):= antitone_nat_of_succ_le (fun t=>(hstep t).MF limit)
 have hAntiLabel: Antitone (fun t=>(states t).labels b):= antitone_nat_of_succ_le (fun t=>(hstep t).Jj limit b)
 have hBridgeLocal:(shifted (u+1)).NV.Adj e.2 b.1:= hAntiLive hBefore hBridge
 have hHighLocal: k+2<(shifted (u+1)).labels b:= hHigh.trans_le (hAntiLabel hBefore)
 have hLocal:= hframe.AT limit e k ∅ (hInternal (t+1+u)) b hMb hBridgeLocal hM hBound hHighLocal
 exact ⟨t+1+u,by omega,by omega,hLocal.1,hLocal.2⟩
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma aP (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1)))
   (hzero:∀e,(states 0).labels e= ell+1) (T tau: ℕ) (e: Fin N ×Fin N) (k: ℕ)
   (hBound: k+1≤ ell) (hBefore: k+1<(states tau).labels e)
   (hFinal:(states T).labels e≤ k+1) (halive: e.1∉(states T).Nm)
   (hInactive:¬(states T).ND.Lh e):
   ∃sigma,tau< sigma∧ sigma< T∧(states sigma).ND.Bg e k:= by
 obtain ⟨t,ht,r,R,hR,hm,P,i,hP,hi,hik,hie,havoid⟩:=
   bB states limit hstep hzero T e (hFinal.trans hBound) halive
 have hPositive:=(states T).positive e
 have hlabel:=((states (t+1)).labelled r R hR P hP).2 i hi
 change (states (t+1)).labels (P.KA i)≤ i+1 at hlabel
 rw [hie] at hlabel
 have hWitnessShort:(states (t+1)).labels e≤ k+1:= by omega
 have hAnti: Antitone (fun u=>(states u).labels e):= antitone_nat_of_succ_le (fun u=>(hstep u).Jj limit e)
 have hAfter: tau< t+1:= by
   by_contra hn
   have hle: t+1≤ tau:= by omega
   have h:= hAnti hle
   change (states tau).labels e≤(states (t+1)).labels e at h
   omega
 have hTrack: R.Ny e k ∅:=⟨P,i,hP,hi,by omega,hie,havoid⟩
 have hNotLast: t+1≠ T:= by
   intro heq
   have hex:(states (t+1)).ND.Lh e:=⟨k,r,R,hR,hTrack⟩
   rw [heq] at hex
   exact hInactive hex
 exact ⟨t+1,hAfter,by omega,r,R,hR,hm,hTrack⟩
lemma aR (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1))) (t: ℕ) (ht: 0< t):
   (states t).ND.n8 (states t).NV:= by
 have h:=((hstep (t-1)).boundary limit).2
 simpa only [Nat.sub_add_cancel (by omega: 1≤ t)] using h
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma bQ (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1))) (hInternal:∀t,(states t).zA)
   (hNo:(states 0).ND.n8 (states 0).NV)
   (hJump:(states 0).ND.M5 (states 0).labels)
   (C: C9 G M) (hC: 1< C.length) (k: ℕ)
   (hForward:(states 0).ND.M7 (C.KA 0))
   (hSettled:∀j,0< j→ j+1< C.length→(states 0).ND.IP (C.KA j))
   (hTarget:(states 0).ND.M7 (C.KA (C.length-1)).swap)
   (hLabel:(states 0).labels (C.KA 0)≤ k+1)
   (hWitness:∃(r: Fin N) (A: Lp G M r) (P: v9 G M r) (i x: ℕ),
     (states 0).ND.state r= some A∧ A.active= some P∧ i< P.length∧ 0< x∧ x< C.length∧
     (P.KA i= C.KA x∨ P.KA i=(C.KA x).swap))
   (hBound: k+C.length≤ ell) (T: ℕ)
   (hLive:∀j,j< 2*C.length-1→(states T).NV.Adj (C.vertex j) (C.vertex (j+1)))
   (hHigh: k+C.length<(states T).labels (C.KA (C.length-1)))
   (hInactive:¬(states T).ND.Lh (C.KA 0)):
   (states 0).ND.IP (C.KA 0):= by
 have hReverse:∀j,0< j→ j< C.length→(states 0).ND.M7 (C.KA j).swap:= by
   intro j hj0 hj
   by_cases hjlast: j= C.length-1
   · rw [hjlast];exact hTarget
   · obtain ⟨r,R,hR,hf,hr⟩:= hSettled j hj0 (by omega)
     exact ⟨r,R,hR,hr⟩
 have hForwardAll:∀j,j+1< C.length→(states 0).ND.M7 (C.KA j):= by
   intro j hj
   by_cases hj0: j= 0
   · rw [hj0];exact hForward
   · obtain ⟨r,R,hR,hf,hr⟩:= hSettled j (by omega) hj
     exact ⟨r,R,hR,hf⟩
 have hAnti: Antitone (fun t=>(states t).NV):= antitone_nat_of_succ_le (fun t=>(hstep t).MF limit)
 have hLive0:∀j,j< 2*C.length-1→(states 0).NV.Adj (C.vertex j) (C.vertex (j+1)):=
   fun j hj=>(hAnti (Nat.zero_le T)) (hLive j hj)
 have hConnect:∀j,j+1< C.length→(states 0).NV.Adj (C.KA j).2 (C.KA (j+1)).1:= by
   intro j hj
   have h:= hLive0 (2*j+1) (by omega)
   convert h using 1<;> congr 1<;> omega
 have hLinks:=(states 0).oL (hInternal 0) hNo C.KA C.length hForwardAll
   (fun j hj=> hReverse (j+1) (by omega) hj) hConnect (fun j hj=> C.s4 j hj)
 by_cases hActive:(states 0).ND.Lh (C.KA 0)
 · exact aA states limit hstep hInternal hJump C hC k hLinks hForward hReverse hLabel
     (Or.inl hActive) hBound T hLive hHigh hInactive
 · obtain ⟨r,A,P,i,x,hA,hP,hi,hx0,hx,hEnd⟩:= hWitness
   exact cE (states 0) (hInternal 0) C hLinks hForward hReverse hLive0 hActive
     A hA P hP i hi x hx0 hx hEnd
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma a0 (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1)))
   (a b: ℕ) (hab: a≤ b) (e: Fin N ×Fin N)
   (hs:(states a).ND.IP e) (halive: e.1∉(states b).Nm):
   (states b).ND.IP e:= by
 let shifted (u: ℕ):= states (a+u)
 have hShift:∀u,jV limit (shifted u) (shifted (u+1)):= by
   intro u
   simpa only [shifted,Nat.add_assoc] using hstep (a+u)
 have hEnd: shifted (b-a)= states b:= by dsimp [shifted];rw [Nat.add_sub_of_le hab]
 have hAlive: e.1∉(shifted (b-a)).Nm:= by rw [hEnd];exact halive
 have h:= bD shifted limit hShift e hs (b-a) hAlive
 rwa [hEnd] at h
lemma aZ (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1)))
   (a b: ℕ) (hab: a≤ b) (e: Fin N ×Fin N)
   (hs:(states a).ND.M7 e) (halive: e.1∉(states b).Nm):
   (states b).ND.M7 e:= by
 let shifted (u: ℕ):= states (a+u)
 have hShift:∀u,jV limit (shifted u) (shifted (u+1)):= by
   intro u
   simpa only [shifted,Nat.add_assoc] using hstep (a+u)
 have hEnd: shifted (b-a)= states b:= by dsimp [shifted];rw [Nat.add_sub_of_le hab]
 have hAlive: e.1∉(shifted (b-a)).Nm:= by rw [hEnd];exact halive
 have h:= bC shifted limit hShift e hs (b-a) hAlive
 rwa [hEnd] at h
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma bE (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1)))
   (hInternal:∀t,(states t).zA)
   (hzero:∀e,(states 0).labels e= ell+1) (T: ℕ)
   (hJump:∀t,t< T→(states t).ND.M5 (states t).labels)
   (C: C9 G M) (hC: 1< C.length) (k: ℕ)
   (hBound: k+C.length≤ ell)
   (hLive:∀j,j< 2*C.length-1→(states T).NV.Adj (C.vertex j) (C.vertex (j+1)))
   (hHigh: k+C.length<(states T).labels (C.KA (C.length-1)))
   (hLabel:(states T).labels (C.KA 0)≤ k+1)
   (hInactive:¬(states T).ND.Lh (C.KA 0))
   (tau: ℕ) (htau: 0< tau) (htT: tau< T)
   (hSettled:∀j,0< j→ j+1< C.length→(states tau).ND.IP (C.KA j))
   (hTarget:(states tau).ND.M7 (C.KA (C.length-1)).swap)
   (hWitness:∃(r: Fin N) (A: Lp G M r) (P: v9 G M r) (i x: ℕ),
     (states tau).ND.state r= some A∧ A.active= some P∧ i< P.length∧ 0< x∧ x< C.length∧
     (P.KA i= C.KA x∨ P.KA i=(C.KA x).swap)):
   wC states C T:= by
 have hAnti: Antitone (fun t=>(states t).NV):= antitone_nat_of_succ_le (fun t=>(hstep t).MF limit)
 have hLiveAt:∀t,t≤ T→∀j,j< 2*C.length-1→(states t).NV.Adj (C.vertex j) (C.vertex (j+1)):=
   fun t ht j hj=> hAnti ht (hLive j hj)
 by_cases hLow:(states tau).labels (C.KA 0)≤ k+1
 · have hForward:= bM states limit hstep hzero tau (C.KA 0)
     (hLow.trans (by omega)) (C.D8 (states tau) (hLiveAt tau htT.le) 0 (by omega)).1
   let shifted (u: ℕ):= states (tau+u)
   have hShift:∀u,jV limit (shifted u) (shifted (u+1)):= by
     intro u
     simpa only [shifted,Nat.add_assoc] using hstep (tau+u)
   have hShiftInternal:∀u,(shifted u).zA:= fun u=> hInternal (tau+u)
   let L:= T-tau
   have hEnd: shifted L= states T:= by dsimp [shifted,L];rw [Nat.add_sub_of_le htT.le]
   have hLiveEnd:∀j,j< 2*C.length-1→(shifted L).NV.Adj (C.vertex j) (C.vertex (j+1)):= by rw [hEnd];exact hLive
   have hHighEnd: k+C.length<(shifted L).labels (C.KA (C.length-1)):= by rw [hEnd];exact hHigh
   have hInactiveEnd:¬(shifted L).ND.Lh (C.KA 0):= by rw [hEnd];exact hInactive
   have hFirst:= bQ shifted limit hShift hShiftInternal
     (aR states limit hstep tau htau) (hJump tau htT)
     C hC k hForward hSettled hTarget hLow hWitness hBound L hLiveEnd hHighEnd hInactiveEnd
   refine ⟨tau,htau,htT,?_,hTarget,?_⟩
   · intro j hj
     by_cases hz: j=0
     · rw [hz];exact hFirst
     · exact hSettled j (by omega) hj
   · obtain ⟨r,A,P,i,x,hA,hP,hi,hx0,hx,he⟩:= hWitness
     exact ⟨r,A,P,i,x,hA,hP,hi,hx,he⟩
 · obtain ⟨sigma,hts,hsT,r,A,hA,hm,P,i,hP,hi,hik,hie,havoid⟩:=
     aP states limit hstep hzero T tau (C.KA 0) k (by omega)
       (by omega) hLabel (C.D8 (states T) hLive 0 (by omega)).1 hInactive
   have hSettledS:∀j,0< j→ j+1< C.length→(states sigma).ND.IP (C.KA j):= by
     intro j hj0 hj
     exact a0 states limit hstep tau sigma hts.le (C.KA j)
       (hSettled j hj0 hj) (C.D8 (states sigma) (hLiveAt sigma hsT.le) j (by omega)).1
   have hTargetS:(states sigma).ND.M7 (C.KA (C.length-1)).swap:=
     aZ states limit hstep tau sigma hts.le _ hTarget
       (C.D8 (states sigma) (hLiveAt sigma hsT.le) (C.length-1) (by omega)).2
   have hForward:(states sigma).ND.M7 (C.KA 0):= by
     have hf:= A.tL P hP i hi
     rw [hie] at hf
     exact ⟨r,A,hA,hf⟩
   have hData:=(states sigma).oM (hInternal sigma)
     (aR states limit hstep sigma (by omega)) C hForward hSettledS hTargetS (hLiveAt sigma hsT.le)
   let shifted (u: ℕ):= states (sigma+u)
   have hShift:∀u,jV limit (shifted u) (shifted (u+1)):= by
     intro u
     simpa only [shifted,Nat.add_assoc] using hstep (sigma+u)
   have hShiftInternal:∀u,(shifted u).zA:= fun u=> hInternal (sigma+u)
   let L:= T-sigma
   have hEnd: shifted L= states T:= by dsimp [shifted,L];rw [Nat.add_sub_of_le hsT.le]
   have hLiveEnd:∀j,j< 2*C.length-1→(shifted L).NV.Adj (C.vertex j) (C.vertex (j+1)):= by rw [hEnd];exact hLive
   have hHighEnd: k+C.length<(shifted L).labels (C.KA (C.length-1)):= by rw [hEnd];exact hHigh
   have hInactiveEnd:¬(shifted L).ND.Lh (C.KA 0):= by rw [hEnd];exact hInactive
   have hFirst:= aB shifted limit hShift hShiftInternal C hC k
     hData.1 hData.2 A hA P hP i hi hik hie hBound L hLiveEnd hHighEnd hInactiveEnd
   refine ⟨sigma,by omega,hsT,?_,hTargetS,?_⟩
   · intro j hj
     by_cases hz: j=0
     · rw [hz];exact hFirst
     · exact hSettledS j (by omega) hj
   · exact ⟨r,A,P,i,0,hA,hP,hi,by omega,Or.inl hie⟩
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma aN (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1)))
   (hInternal:∀t,(states t).zA)
   (hzero:∀e,(states 0).labels e= ell+1) (T: ℕ)
   (C: C9 G M) (hC: C.length=2) (k: ℕ)
   (hBound: k+C.length≤ ell)
   (hLive:∀j,j< 2*C.length-1→(states T).NV.Adj (C.vertex j) (C.vertex (j+1)))
   (hHigh: k+C.length<(states T).labels (C.KA (C.length-1)))
   (hLabel:(states T).labels (C.KA 0)≤ k+1)
   (hInactive:¬(states T).ND.Lh (C.KA 0)):
   wC states C T:= by
 have hMb: M.Adj (C.KA 1).1 (C.KA 1).2:=
   (C.MG 2 (by omega)).2 (by decide)
 have hBridge:(states T).NV.Adj (C.KA 0).2 (C.KA 1).1:= hLive 1 (by omega)
 have hH: k+2<(states T).labels (C.KA 1):= by simpa only [hC] using hHigh
 obtain ⟨t,ht,htT,hsettled,hactive⟩:= aF states limit hstep hInternal hzero T
   (C.KA 0) (C.KA 1) k hLabel hInactive hMb (C.s4 0 (by omega))
   (by omega) (C.D8 (states T) hLive 0 (by omega)).1 hBridge hH
 obtain ⟨bound,r,A,hA,P,i,hP,hi,hib,hie,havoid⟩:= hactive
 have hReach:= A.tL P hP i hi
 rw [hie] at hReach
 refine ⟨t,ht,htT,?_,?_,?_⟩
 · intro j hj
   have hj0: j=0:= by omega
   rw [hj0];exact hsettled
 · simpa only [hC] using (show (states t).ND.M7 (C.KA 1).swap from ⟨r,A,hA,hReach⟩)
 · exact ⟨r,A,P,i,1,hA,hP,hi,by omega,Or.inr hie⟩
lemma aK (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1)))
   (hInternal:∀t,(states t).zA)
   (hzero:∀e,(states 0).labels e= ell+1) (T: ℕ)
   (hJump:∀t,t< T→(states t).ND.M5 (states t).labels)
   (C: C9 G M) (hC: 1< C.length) (k: ℕ)
   (hBound: k+C.length≤ ell)
   (hLive:∀j,j< 2*C.length-1→(states T).NV.Adj (C.vertex j) (C.vertex (j+1)))
   (hHigh: k+C.length<(states T).labels (C.KA (C.length-1)))
   (hLabel:∀j,j+1< C.length→(states T).labels (C.KA j)≤ k+j+1)
   (hInactive:∀j,j+1< C.length→¬(states T).ND.Lh (C.KA j)):
   wC states C T:= by
 have general:∀n,∀(C: C9 G M),C.length=n→ 1<C.length→∀k,
     k+C.length≤ ell→
     (∀j,j<2*C.length-1→(states T).NV.Adj (C.vertex j) (C.vertex (j+1)))→
     k+C.length<(states T).labels (C.KA (C.length-1))→
     (∀j,j+1<C.length→(states T).labels (C.KA j)≤ k+j+1)→
     (∀j,j+1<C.length→¬(states T).ND.Lh (C.KA j))→
     wC states C T:= by
   intro n
   induction n using Nat.strong_induction_on with
   | h n ih =>
     intro C hn hC k hBound hLive hHigh hLabel hInactive
     by_cases hb: C.length=2
     · exact aN states limit hstep hInternal hzero T C hb k hBound hLive hHigh
         (by simpa using hLabel 0 (by omega)) (hInactive 0 (by omega))
     · let Q:= C.LB hC
       have hQlen: Q.length= C.length-1:= rfl
       have hQ: 1<Q.length:= by omega
       have hQB:(k+1)+Q.length≤ ell:= by omega
       have hQL:∀j,j<2*Q.length-1→(states T).NV.Adj (Q.vertex j) (Q.vertex (j+1)):= by
         intro j hj
         have hh:= hLive (j+2) (by omega)
         change (states T).NV.Adj (C.vertex (j+2)) (C.vertex (j+1+2))
         simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
       have hQHigh:(k+1)+Q.length<(states T).labels (Q.KA (Q.length-1)):= by
         rw [C.DA]
         omega
       have hQLabel:∀j,j+1<Q.length→(states T).labels (Q.KA j)≤(k+1)+j+1:= by
         intro j hj
         rw [C.FH]
         have hh:= hLabel (j+1) (by omega)
         omega
       have hQInactive:∀j,j+1<Q.length→¬(states T).ND.Lh (Q.KA j):= by
         intro j hj
         rw [C.FH]
         exact hInactive (j+1) (by omega)
       obtain ⟨tau,htau,htT,hSettled,hTarget,r,A,P,i,x,hA,hP,hi,hx,he⟩:=
         ih Q.length (by omega) Q rfl hQ (k+1) hQB hQL hQHigh hQLabel hQInactive
       have hSettledC:∀j,0<j→ j+1<C.length→(states tau).ND.IP (C.KA j):= by
         intro j hj0 hj
         have hh:= hSettled (j-1) (by omega)
         rw [C.FH] at hh
         simpa only [Nat.sub_add_cancel (by omega: 1≤j)] using hh
       have hTargetC:(states tau).ND.M7 (C.KA (C.length-1)).swap:= by
         rwa [C.DA] at hTarget
       apply bE states limit hstep hInternal hzero T hJump C hC k hBound hLive hHigh
         (by simpa using hLabel 0 (by omega)) (hInactive 0 (by omega)) tau htau htT hSettledC hTargetC
       refine ⟨r,A,P,i,x+1,hA,hP,hi,by omega,by omega,?_⟩
       change P.KA i=(C.LB hC).KA x∨ P.KA i=((C.LB hC).KA x).swap at he
       simpa only [C.FH] using he
 exact general C.length C rfl hC k hBound hLive hHigh hLabel hInactive
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma a4 (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1)))
   (hInternal:∀t,(states t).zA)
   (hzero:∀e,(states 0).labels e= ell+1) (T: ℕ)
   (hJump:∀t,t< T→(states t).ND.M5 (states t).labels)
   (C: C9 G M) (hC: 1< C.length) (k: ℕ)
   (hBound: k+C.length≤ ell)
   (hLive:∀j,j< 2*C.length-1→(states T).NV.Adj (C.vertex j) (C.vertex (j+1)))
   (hHigh: k+C.length<(states T).labels (C.KA (C.length-1)))
   (hLabel:∀j,j+1< C.length→(states T).labels (C.KA j)≤ k+j+1)
   (hInactive:∀j,j+1< C.length→¬(states T).ND.Lh (C.KA j)):
   ∀j,j+1< C.length→(states T).ND.IP (C.KA j):= by
 obtain ⟨tau,htau,htT,hSettled,hTarget,hActive⟩:=
   aK states limit hstep hInternal hzero T hJump C hC k hBound hLive hHigh hLabel hInactive
 intro j hj
 exact a0 states limit hstep tau T htT.le (C.KA j)
   (hSettled j hj) (C.D8 (states T) hLive j (by omega)).1
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma bO (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1)))
   (hInternal:∀t,(states t).zA)
   (hzero:∀e,(states 0).labels e= ell+1) (T: ℕ)
   (hPast:∀t,t< T→(states t).ND.M5 (states t).labels)
   {S: tI G M ell} {es: List (Fin N ×Fin N)}
   (hPass: M2 true es ((states T).IX limit) S)
   (hNow: S.ND.M5 S.labels) {x y: Fin N} (R: y7 S x y):
   IN R.state.tree R.NX S.labels:= by
 intro i hi hshort
 by_cases hOld: i< R.J5.length
 · have he:= R.J5.I4 R.DL i hOld
   rw [he] at hshort ⊢
   exact hNow R.root R.state R.present R.J5 R.Lq i hOld hshort
 · have hAfter: R.J5.length≤ i:= by omega
   let k:= R.J5.length
   have hkP: k< R.targetPath.length:= by
     change R.J5.length< R.NX.length+1
     have h:= R.DL.1
     omega
   let C:= R.targetPath.F8 k hkP
   have hCLen: C.length= R.NX.length+1-k:= rfl
   have hC: 1<C.length:= by dsimp [k] at hCLen;omega
   have hLive:∀j,j< 2*C.length-1→ S.NV.Adj (C.vertex j) (C.vertex (j+1)):=
     R.targetPath.uQ k hkP S.NV R.CR
   have hLiveStart:∀j,j< 2*C.length-1→(states T).NV.Adj (C.vertex j) (C.vertex (j+1)):=
     fun j hj=> hPass.MF (hLive j hj)
   have hArc (j: ℕ) (hj: j+1<C.length): C.KA j= R.NX.KA (k+j):= by
     rw [R.targetPath.xI,R.p8]
     omega
   have hEnd: C.KA (C.length-1)=(y,R.NW):= by
     rw [R.targetPath.uP,R.v0]
   have hInactiveNow (j: ℕ) (hj: j+1<C.length):¬S.ND.Lh (C.KA j):= by
     rw [hArc j hj]
     exact R.BS (k+j) (by omega) (by dsimp [k];omega)
   have hLabelStart:∀j,j+1<C.length→(states T).labels (C.KA j)≤ k+j+1:= by
     intro j hj
     have hEq:= hPass.w9 (C.KA j)
       (C.D8 S hLive j (by omega)).1 (hInactiveNow j hj)
     change S.labels (C.KA j)=(states T).labels (C.KA j) at hEq
     rw [←hEq,hArc j hj]
     exact R.labelled.2 (k+j) (by omega)
   have hInactiveStart:∀j,j+1<C.length→¬(states T).ND.Lh (C.KA j):= by
     intro j hj hActive
     have hNo:= hPass.w8 (C.KA j)
       (C.D8 S hLive j (by omega)).1 (hInactiveNow j hj)
     exact hNo ((states T).G9 limit (C.KA j) hActive)
   have hTotal: k+C.length= R.NX.length+1:= by have h:=R.DL.1;dsimp [k] at hCLen ⊢;omega
   have hHigh: k+C.length<(states T).labels (C.KA (C.length-1)):= by
     rw [hEnd,hTotal]
     exact R.My.trans_le (hPass.Jj (y,R.NW))
   have hSettled:= a4 states limit hstep hInternal hzero T hPast C hC k
     (by rw [hTotal];exact R.bound) hLiveStart hHigh hLabelStart hInactiveStart
   have hj: i-k+1<C.length:= by omega
   have he: C.KA (i-k)= R.NX.KA i:= by
     rw [hArc (i-k) hj]
     congr 1
     omega
   have hSet:= hSettled (i-k) hj
   rw [he] at hSet
   have hAlive:(R.NX.KA i).1∉(states T).Nm:= by
     rw [←he]
     exact (C.D8 (states T) hLiveStart (i-k) (by omega)).1
   have hBegin:((states T).IX limit).ND.IP (R.NX.KA i):=
     (Bf.begin (states T) limit).lP _ hAlive hSet
   have hHere:= hPass.lP (R.NX.KA i)
     (S.k7 R.root R.state R.present _
       (R.state.tree.EA R.NX R.inside (R.NX.mem_support (2*i+1) (by omega)))) hBegin
   obtain ⟨r,A,hA,hf,hr⟩:= hHere
   exact S.ND.AJ (R.NX.KA i).swap R.state R.present
     (R.state.tree.EA R.NX R.inside (R.NX.mem_support (2*i+2) (by omega))) ⟨r,A,hA,hr⟩
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma a3 (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1)))
   (hInternal:∀t,(states t).zA)
   (hzero:∀e,(states 0).labels e= ell+1) (T: ℕ)
   (hPast:∀t,t< T→(states t).ND.M5 (states t).labels)
   {S U: tI G M ell} {es: List (Fin N ×Fin N)}
   (h: M2 true es S U) (pre: List (Fin N ×Fin N))
   (hPre: M2 true pre ((states T).IX limit) S)
   (hNow: S.ND.M5 S.labels): U.ND.M5 U.labels:= by
 induction h generalizing pre with
 | nil => exact hNow
 | @cons x y es S V U step rest ih =>
   have hV:= step.Ad hNow (fun R=> bO states limit hstep hInternal hzero T hPast hPre hNow R)
   exact ih (pre++[(x,y)]) (hPre.append (M2.cons step (M2.nil V))) hV
lemma aS (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1)))
   (hInternal:∀t,(states t).zA)
   (hzero:∀e,(states 0).labels e= ell+1)
   (hInitial:(states 0).ND.M5 (states 0).labels):
   ∀T,(states T).ND.M5 (states T).labels:= by
 intro T
 induction T using Nat.strong_induction_on with
 | h T ih =>
   cases T with
   | zero => exact hInitial
   | succ T =>
     obtain ⟨U,O,hBundle,hExtra⟩:= hstep T
     obtain ⟨Oe,Oc,V,W,hExt,hCheck,hU⟩:= hBundle
     have hPast:∀t,t<T→(states t).ND.M5 (states t).labels:= fun t ht=> ih t (by omega)
     have hBegin:=(states T).F3 limit (ih T (by omega))
     obtain ⟨V0,hVpass,hVprune⟩:=hExt.Np
     have hV0:= a3 states limit hstep hInternal hzero T hPast hVpass []
       (M2.nil _) hBegin
     have hV: V.ND.M5 V.labels:= by
       rw [hVprune.LG,hVprune.LO]
       exact hV0
     have hW:= hCheck.F4 ((V.rC limit).xB (V.HF limit hV))
     have hUJump: U.ND.M5 U.labels:= by rw [hU];exact W.BT hW
     exact hExtra.F4 hUJump
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
def cO (limit: ℕ) (S T: tI G M ell) (r: Fin N): Prop:=
 ∃(O: J3 G) (U: tI G M ell) (R: Lp G M r) (P: v9 G M r),
   y5 true O.edges (S.IX limit) U∧
   (U.rC limit).ND.state r=some R∧
   R.active=some P∧ P.length=0∧ R.NU=false∧ R.modified=false∧ fZ limit U T
lemma jV.CH {S T: tI G M ell} (limit: ℕ)
   (h: jV limit S T) (r: Fin N) (hAlive: r∉T.Nm)
   (hActive: r∈S.ND.IS) (hLost: r∉T.ND.IS): cO limit S T r:= by
 obtain ⟨U,O,hBundle,hExtra⟩:= h
 obtain ⟨Oe,Oc,V,W,hExt,hCheck,hU⟩:= hBundle
 have hAliveW: r∉W.Nm:= by
   intro hr
   exact hAlive (hExtra.In (by rw [hU];exact hr))
 have hAliveV: r∉V.Nm:= fun hr=> hAliveW (hCheck.In hr)
 have hBegin: r∈(S.IX limit).ND.IS:=
   S.ND.Bm (fun _ R=>R.IX limit) (fun _ _=>rfl) (fun _ _=>rfl) r hActive
 have hV:= hExt.qO r hAliveV hBegin
 have hHeld: r∈(V.rC limit).ND.IS:=
   V.ND.Bm (fun _ R=>R.rC limit) (fun _ _=>rfl) (fun _ _=>rfl) r hV
 have hNoBack: r∉(V.rC limit).Dk.ND.IS:= by
   intro hBack
   have hW:= hCheck.qO r hAliveW hBack
   have hInc: r∈W.z9.ND.IS:= W.ND.Bm
     (fun _ R=>R.z8 W.NV W.MF) (fun _ R=>R.fA W.NV W.MF)
     (fun _ _=>rfl) r hW
   have hUU: r∈U.ND.IS:= by rw [hU];exact hInc
   exact hLost (hExtra.qO r hAlive hUU)
 obtain ⟨R,hR,hRa⟩:=((V.rC limit).ND.xO _ r).mp hHeld
 have hRLost:¬R.zS.active.isSome:= by
   intro hnew
   apply hNoBack
   apply ((V.rC limit).Dk.ND.xO _ r).mpr
   refine ⟨R.zS,?_,hnew⟩
   change ((V.rC limit).ND.state r).map (fun R=>R.zS)=some R.zS
   rw [hR];rfl
 obtain ⟨P,hP,hLen,hHeldFlag,hMod⟩:= R.fS hRa hRLost
 refine ⟨Oe,V,R,P,hExt,hR,hP,hLen,hHeldFlag,hMod,Oc,W,O,hCheck,?_⟩
 simpa only [←hU] using hExtra
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma fZ.vT {limit: ℕ} {U T: tI G M ell}
   (h: fZ limit U T) {r: Fin N} (R: Lp G M r) (hR: T.ND.state r=some R):
   ∃B,U.ND.state r=some B∧ R.tree.vertices=B.tree.vertices:= by
 obtain ⟨O,V,K,hV,hT⟩:= h
 have hInc:= hT.tS R hR
 change (V.ND.state r).map (fun A=>A.z8 V.NV V.MF)=some R at hInc
 obtain ⟨C,hC,hCR⟩:= Option.map_eq_some_iff.mp hInc
 have hBack:= hV.tS C hC
 change ((U.rC limit).ND.state r).map (fun A=>A.zS)=some C at hBack
 obtain ⟨D,hD,hDC⟩:= Option.map_eq_some_iff.mp hBack
 change (U.ND.state r).map (fun A=>A.rC limit)=some D at hD
 obtain ⟨B,hB,hBD⟩:= Option.map_eq_some_iff.mp hD
 refine ⟨B,hB,?_⟩
 rw [←hCR,C.fA,←hDC,←hBD]
 unfold Lp.zS
 split_ifs<;> rfl
lemma jV.c1 (limit: ℕ) (h: jV limit S T)
   {r: Fin N} (hNo: r∉S.ND.IS) (Q: Lp G M r) (hQ: T.ND.state r=some Q):
   ∃B,S.ND.state r=some B∧ Q.tree.vertices ⊆B.tree.vertices:= by
 obtain ⟨U,O,hBundle,hExtra⟩:= h
 obtain ⟨Oe,Oc,V,W,hExt,hCheck,hU⟩:= hBundle
 have hAfter: fZ limit V T:=⟨Oc,W,O,hCheck,by simpa only [←hU] using hExtra⟩
 obtain ⟨C,hC,hQC⟩:= hAfter.vT Q hQ
 have hNoBegin: r∉(S.IX limit).ND.IS:=
   fun ha=> hNo ((Bf.begin S limit).qP ha)
 obtain ⟨D,hD,hCD⟩:= hExt.c1 hNoBegin C hC
 change (S.ND.state r).map (fun B=>B.IX limit)=some D at hD
 obtain ⟨B,hB,hBD⟩:= Option.map_eq_some_iff.mp hD
 refine ⟨B,hB,?_⟩
 rw [hQC]
 rw [←hBD] at hCD
 exact hCD
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
variable {S T: tI G M ell}
lemma fZ.Ks {S T: tI G M ell} {limit: ℕ}
   (h: fZ limit S T): T.ND.Lm limit:= by
 intro r R hR hLarge
 obtain ⟨O,V,K,hV,hT⟩:= h
 have hInc:= hT.tS R hR
 change (V.ND.state r).map (fun A=>A.z8 V.NV V.MF)=some R at hInc
 obtain ⟨C,hC,hCR⟩:= Option.map_eq_some_iff.mp hInc
 have hBack:= hV.tS C hC
 change ((S.rC limit).ND.state r).map (fun A=>A.zS)=some C at hBack
 obtain ⟨D,hD,hDC⟩:= Option.map_eq_some_iff.mp hBack
 change (S.ND.state r).map (fun A=>A.rC limit)=some D at hD
 obtain ⟨B,hB,hBD⟩:= Option.map_eq_some_iff.mp hD
 have hRV: R.tree.vertices=B.tree.vertices:= by
   rw [←hCR,C.fA,←hDC,D.eT,←hBD]
   rfl
 have hRH: R.NU=(B.rC limit).NU:= by
   rw [←hCR]
   change C.NU=(B.rC limit).NU
   rw [←hDC,D.mC,←hBD]
 rw [hRH]
 change (B.NU|| decide (limit≤B.tree.vertices.card))=true
 rw [hRV] at hLarge
 simp only [decide_eq_true hLarge,Bool.or_true]
lemma jV.Ks {S T: tI G M ell} (limit: ℕ)
   (h: jV limit S T): T.ND.Lm limit:= by
 obtain ⟨U,O,hB,hExtra⟩:= h
 obtain ⟨Oe,Oc,V,W,hExt,hCheck,hU⟩:= hB
 exact (show fZ limit V T from ⟨Oc,W,O,hCheck,by simpa only [←hU] using hExtra⟩).Ks
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma y5.p5 {S T: tI G M ell} {L A: ℕ}
   (hA: 2≤ A) (hSize:∀r R,S.ND.state r=some R→ R.tree.vertices.card≤ A)
   (hHold: S.ND.Lm L) {es: List (Fin N ×Fin N)}
   (h: y5 true es (S.IX L) T):
   ∀r R,T.ND.state r=some R→ R.tree.vertices.card≤ A+L*ell:= by
 obtain ⟨U,hPass,hPrune⟩:=h.Np
 rw [hPrune.LG]
 exact hPass.p5 hA hSize hHold
lemma jV.p5 {S T: tI G M ell} {A: ℕ}
   (L: ℕ) (h: jV L S T) (hA: 2≤A)
   (hSize:∀r R,S.ND.state r=some R→ R.tree.vertices.card≤A) (hHold: S.ND.Lm L):
   ∀r R,T.ND.state r=some R→ R.tree.vertices.card≤A+L*ell:= by
 obtain ⟨U,O,hBundle,hExtra⟩:= h
 obtain ⟨Oe,Oc,V,W,hExt,hCheck,hU⟩:= hBundle
 have hAfter: fZ L V T:=⟨Oc,W,O,hCheck,by simpa only [←hU] using hExtra⟩
 have hBound:= hExt.p5 hA hSize hHold
 intro r R hR
 obtain ⟨B,hB,hRB⟩:= hAfter.vT R hR
 rw [hRB]
 exact hBound r B hB
lemma bP (states: ℕ→ tI G M ell) (L: ℕ)
   (hstep:∀t,jV L (states t) (states (t+1)))
   (hSize0:∀r R,(states 0).ND.state r=some R→ R.tree.vertices.card≤2)
   (hHold0:(states 0).ND.Lm L):
   ∀T r R,(states T).ND.state r=some R→ R.tree.vertices.card≤2+T*(L*ell):= by
 have hHold:∀t,(states t).ND.Lm L:= by
   intro t
   cases t with
   | zero => exact hHold0
   | succ t => exact (hstep t).Ks L
 intro T
 induction T with
 | zero => simpa using hSize0
 | succ T ih =>
   intro r R hR
   have hBound:=(hstep T).p5 L (by omega) ih (hHold T) r R hR
   convert hBound using 1<;> ring
end Be
end
noncomputable section
namespace Be
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)}
lemma rD {S: tI G M ell} {size: ℕ} (L: ℕ)
   (hSize:∀r V,S.ND.state r=some V→ V.tree.vertices.card≤ size):
   ∀r V,((S.rC L).Dk).ND.state r=some V→ V.tree.vertices.card≤ size:= by
 intro r V hV
 change ((S.ND.state r).map (fun V=>V.rC L)).map (fun V=>V.zS)=some V at hV
 obtain ⟨W,hW,hWV⟩:=Option.map_eq_some_iff.mp hV
 obtain ⟨Q,hQ,hQW⟩:=Option.map_eq_some_iff.mp hW
 rw [←hWV,W.eT,←hQW]
 exact hSize r Q hQ
lemma HB {S: tI G M ell} {size: ℕ}
   (hSize:∀r V,S.ND.state r=some V→ V.tree.vertices.card≤ size):
   ∀r V,S.z9.ND.state r=some V→ V.tree.vertices.card≤ size:= by
 intro r V hV
 change (S.ND.state r).map (fun V=>V.z8 S.NV S.MF)=some V at hV
 obtain ⟨Q,hQ,hQV⟩:=Option.map_eq_some_iff.mp hV
 rw [←hQV,Q.fA]
 exact hSize r Q hQ
lemma Kb {S: tI G M ell} {size: ℕ}
   (hSize:∀r V,S.ND.state r=some V→ V.tree.vertices.card≤ size):
   ∀U es,M2 false es S U→∀r V,U.ND.state r=some V→ V.tree.vertices.card≤ size:= by
 intro U es hPass r V hV
 exact hSize r V (hPass.tS V hV)
lemma y5.Kb {S T: tI G M ell} {es: List (Fin N ×Fin N)} {size: ℕ}
   (h: y5 false es S T)
   (hSize:∀r V,S.ND.state r=some V→ V.tree.vertices.card≤ size):
   ∀r V,T.ND.state r=some V→ V.tree.vertices.card≤ size:= by
 obtain ⟨U,hPass,hPrune⟩:=h.Np
 intro r V hV
 rw [hPrune.LG] at hV
 exact Be.Kb hSize U es hPass r V hV
lemma s1 {V: Type} [DecidableEq V] (D E F: Finset V) (target m: ℕ)
   (hD: 3*target*D.card≤ m) (hE: 3*target*E.card≤ m) (hF: 3*target*F.card≤ m):
   target*(D∪E∪F).card≤ m:= by
 have hCard:(D∪E∪F).card≤ D.card+E.card+F.card:=
   (card_union_le (D∪E) F).trans (Nat.add_le_add_right (card_union_le D E) F.card)
 have hh:=Nat.mul_le_mul_left (3*target) hCard
 nlinarith
end Be
end
noncomputable section
namespace Be.Fi
variable {K: Type} {N ell size B aSize: ℕ} {G M: SimpleGraph (Fin N)} {S: tI G M ell}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M} {data: Fin N→ Ln}
   (h: Fi S ids hi out hOut data)
   (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K) (hS: 2≤ size)
   (hOracle: qH A k G ids size B)
include h hS hOracle in
lemma j6 (L target: ℕ) (hTarget: 0<target) (hB: 0<B)
   (hOpt: optimum G≤ B*matchingSize M) (hBase: 2≤ aSize)
   (hSize:∀r V,S.ND.state r=some V→ V.tree.vertices.card≤ aSize)
   (hHold: S.ND.Lm L) (hFit: aSize+L*ell≤ size):
   ∃(NP: IJ) (T: tI G M ell) (D: Finset (Fin N)),
     NP.1<3*target*(2*size*B)*(2*ell+B)∧
     NP.2.1<3*target*(2*size*B)*(2*ell+B)∧
     NP.2.2<3*target*(2*size*B)*(2*ell+B)∧
     target*D.card≤ matchingSize M∧ jV L S T∧ S.Fh T D∧
     Fi T ids hi out hOut (execute (oQ A k size ell L NP) G () ids data):= by
 let dataBegin:=execute (n9.begin L).program G () ids data
 have hBegin: Fi (S.IX L) ids hi out hOut dataBegin:=
   (n9.begin L).encoding S ids hi out hOut data h
 have hBoundExt:∀U es,M2 true es (S.IX L) U→
     ∀r V,U.ND.state r=some V→ V.tree.vertices.card≤ size:=by
   intro U es hPass r V hV
   exact (hPass.p5 hBase hSize hHold r V hV).trans hFit
 obtain ⟨j1,U,es1,D1,hJ1,hSmall1,hExt,hCover1,hEncoding1⟩:=hBegin.GP A k hS true
   hBoundExt hOracle (3*target) (by positivity) hB hOpt (fun _=>S.iI L)
 let dataU:=execute (IC A k size ell true j1) G () ids dataBegin
 let dataHold:=execute (n9.hold L).program G () ids dataU
 let dataBack:=execute n9.backtrack.program G () ids dataHold
 have hHoldEncoding: Fi (U.rC L) ids hi out hOut dataHold:=
   (n9.hold L).encoding U ids hi out hOut dataU hEncoding1
 have hBackEncoding: Fi ((U.rC L).Dk) ids hi out hOut dataBack:=
   n9.backtrack.encoding _ ids hi out hOut dataHold hHoldEncoding
 have hSizeU:∀r V,U.ND.state r=some V→ V.tree.vertices.card≤ size:=by
   intro r V hV
   exact (hExt.p5 hBase hSize hHold r V hV).trans hFit
 have hSizeBack:=rD L hSizeU
 obtain ⟨j2,V,es2,D2,hJ2,hSmall2,hCheck,hCover2,hEncoding2⟩:=hBackEncoding.GP A k hS false
   (Be.Kb hSizeBack) hOracle (3*target) (by positivity) hB hOpt (fun hh=>Bool.noConfusion hh)
 let dataV:=execute (IC A k size ell false j2) G () ids dataBack
 let dataInclude:=execute (rG size ell) G () ids dataV
 have hSizeV:=hCheck.Kb hSizeBack
 have hIncludeEncoding: Fi V.z9 ids hi out hOut dataInclude:=
   hEncoding2.i1 hSizeV hS
 obtain ⟨j3,T,es3,D3,hJ3,hSmall3,hExtra,hCover3,hEncoding3⟩:=hIncludeEncoding.GP A k hS false
   (Be.Kb (HB hSizeV)) hOracle (3*target) (by positivity) hB hOpt
   (fun hh=>Bool.noConfusion hh)
 refine ⟨(j1,j2,j3),T,D1∪D2∪D3,hJ1,hJ2,hJ3,?_,?_,?_,?_⟩
 · exact s1 D1 D2 D3 target (matchingSize M) hSmall1 hSmall2 hSmall3
 · exact ⟨V.z9,⟨es3⟩,⟨⟨es1⟩,⟨es2⟩,U,V,hExt,hCheck,rfl⟩,hExtra⟩
 · intro u v hLive hu hv huD hvD
   have huV: u∉V.Nm:=fun hh=>hu (hExtra.In hh)
   have hvV: v∉V.Nm:=fun hh=>hv (hExtra.In hh)
   have huU: u∉U.Nm:=fun hh=>huV (hCheck.In hh)
   have hvU: v∉U.Nm:=fun hh=>hvV (hCheck.In hh)
   have hU:=hCover1 u v hLive huU hvU
     (fun hh=>huD (mem_union_left _ (mem_union_left _ hh)))
     (fun hh=>hvD (mem_union_left _ (mem_union_left _ hh)))
   have hV:=hCover2 u v hU huV hvV
     (fun hh=>huD (mem_union_left _ (mem_union_right _ hh)))
     (fun hh=>hvD (mem_union_left _ (mem_union_right _ hh)))
   exact hCover3 u v hV hu hv (fun hh=>huD (mem_union_right _ hh)) (fun hh=>hvD (mem_union_right _ hh))
 · simp only [oQ,AZ]
   exact hEncoding3
end Be.Fi
end
noncomputable section
namespace Be
variable {N ell: ℕ} {G M: SimpleGraph (Fin N)}
lemma jV.FO (S: tI G M ell) (L: ℕ):
   ∃T,jV L S T:= by
 obtain ⟨U,es,hPass,hClosed,hFlags⟩:=fE S L
 have hExt: y5 true es (S.IX L) U.Cs:=by
   simpa only [List.append_nil] using hPass.Mh.EX ((M2.nil U).qW hClosed)
 let V:=((U.Cs.rC L).Dk).vL
 have hCheck: y5 false [] ((U.Cs.rC L).Dk) V:=
   (M2.nil _).Bt
 have hExtra: y5 false [] V.z9 V.z9.vL:=
   (M2.nil _).Bt
 exact ⟨V.z9.vL,V.z9,⟨[]⟩,
   ⟨⟨es⟩,⟨[]⟩,U.Cs,V,hExt,hCheck,rfl⟩,hExtra⟩
end Be
end
noncomputable section
namespace Be
structure Fj {N ell: ℕ} {G M: SimpleGraph (Fin N)}
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (out: Fin N→ Option ℕ)
   (hOut: ReportsMatching G ids out M) (P L t: ℕ) where
 state: tI G M ell
 data: Fin N→ Ln
 encoding: t≤ P→ Fi state ids hi out hOut data
 size:∀r V,state.ND.state r=some V→ V.tree.vertices.card≤ 2+t*(L*ell)
 hold: state.ND.Lm L
namespace Fj
variable {K: Type} {N ell size B P L t: ℕ} {G M: SimpleGraph (Fin N)}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M}
   (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K) (hS: 2≤ size)
   (hOracle: qH A k G ids size B)
   (target: ℕ) (hTarget: 0<target) (hB: 0<B) (hOpt: optimum G≤ B*matchingSize M)
   (hFit: 2+P*(L*ell)≤ size) (X: Fj (ell:=ell) ids hi out hOut P L t)
structure Mt where
 state: tI G M ell
 data: Fin N→ Ln
 NP: IJ
 omitted: Finset (Fin N)
 Ly: jV L X.state state
 encoding: t+1≤ P→ Fi state ids hi out hOut data
 Kf: t<P→ data=execute (oQ A k size ell L NP) G () ids X.data
 K9: t<P→ NP.1<3*target*(2*size*B)*(2*ell+B)∧
   NP.2.1<3*target*(2*size*B)*(2*ell+B)∧ NP.2.2<3*target*(2*size*B)*(2*ell+B)
 small: t<P→ target*omitted.card≤ matchingSize M
 cover: X.state.Fh state omitted
def MY: X.Mt (ell:=ell) (size:=size) (B:=B) A k target:=Classical.choice (by
 by_cases ht: t<P
 · have hSize: 2+t*(L*ell)+L*ell≤ size:=by
     have hh:=Nat.mul_le_mul_right (L*ell) (by omega: t+1≤P)
     calc
       2+t*(L*ell)+L*ell=2+(t+1)*(L*ell):=by ring
       _≤ 2+P*(L*ell):=Nat.add_le_add_left hh 2
       _≤ size:=hFit
   obtain ⟨NP,T,D,hJ1,hJ2,hJ3,hSmall,hCert,hCover,hEncoding⟩:=
     (X.encoding (Nat.le_of_lt ht)).j6 A k hS hOracle L target hTarget hB hOpt
       (by omega) X.size X.hold hSize
   exact ⟨⟨T,execute (oQ A k size ell L NP) G () ids X.data,NP,D,
     hCert,fun _=>hEncoding,fun _=>rfl,fun _=>⟨hJ1,hJ2,hJ3⟩,fun _=>hSmall,hCover⟩⟩
 · obtain ⟨T,hCert⟩:=jV.FO X.state L
   exact ⟨⟨T,X.data,(0,0,0),univ,hCert,fun hNew=>(ht (by omega)).elim,
     fun hlt=>(ht hlt).elim,fun hlt=>(ht hlt).elim,fun hlt=>(ht hlt).elim,
     by intro u v hLive hu hv huD hvD;exact (huD (mem_univ _)).elim⟩⟩)
def next: Fj (ell:=ell) ids hi out hOut P L (t+1) where
 state:=(X.MY A k hS hOracle target hTarget hB hOpt hFit).state
 data:=(X.MY A k hS hOracle target hTarget hB hOpt hFit).data
 encoding:=(X.MY A k hS hOracle target hTarget hB hOpt hFit).encoding
 size:=by
   intro r V hV
   have hh:=((X.MY A k hS hOracle target hTarget hB hOpt hFit).Ly).p5 L
     (by omega) X.size X.hold r V hV
   convert hh using 1<;> ring
 hold:=(X.MY A k hS hOracle target hTarget hB hOpt hFit).Ly.Ks L
end Fj
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma y5.oP {S T: tI G M ell}
   {es: List (Fin N ×Fin N)} (h: y5 false es S T) (size: ℕ)
   (hSize:∀r R,S.ND.state r=some R→ R.tree.vertices.card≤ size)
   (hBudget: S.Nm.card≤ 2*size*S.found.card): T.Nm.card≤ 2*size*T.found.card:= by
 obtain ⟨U,hPass,hPrune⟩:=h.Np
 rw [hPrune.KY,hPrune.MC]
 exact hPass.oP size hSize hBudget
lemma y5.gD {S T: tI G M ell}
   {es: List (Fin N ×Fin N)} {L A: ℕ} (h: y5 true es (S.IX L) T)
   (hA: 2≤ A) (hSize:∀r R,S.ND.state r=some R→ R.tree.vertices.card≤ A)
   (hHold: S.ND.Lm L)
   (hBudget: S.Nm.card≤ 2*(A+L*ell)*S.found.card):
   T.Nm.card≤ 2*(A+L*ell)*T.found.card:= by
 obtain ⟨U,hPass,hPrune⟩:=h.Np
 rw [hPrune.KY,hPrune.MC]
 exact b0 S L A hA hSize hHold hPass [] (M2.nil _) hBudget
lemma fZ.EK {S T: tI G M ell} {L: ℕ}
   (h: fZ L S T) (size: ℕ)
   (hSize:∀r R,S.ND.state r=some R→ R.tree.vertices.card≤ size)
   (hBudget: S.Nm.card≤ 2*size*S.found.card): T.Nm.card≤ 2*size*T.found.card:= by
 obtain ⟨O,V,K,hV,hT⟩:= h
 have hBackSize:∀r R,(S.rC L).Dk.ND.state r=some R→ R.tree.vertices.card≤ size:= by
   intro r R hR
   change ((S.rC L).ND.state r).map (fun B=>B.zS)=some R at hR
   obtain ⟨C,hC,hCR⟩:= Option.map_eq_some_iff.mp hR
   change (S.ND.state r).map (fun B=>B.rC L)=some C at hC
   obtain ⟨B,hB,hBC⟩:= Option.map_eq_some_iff.mp hC
   rw [←hCR,C.eT,←hBC]
   exact hSize r B hB
 have hBudgetV:=hV.oP size hBackSize hBudget
 have hIncludeSize:∀r R,V.z9.ND.state r=some R→ R.tree.vertices.card≤ size:= by
   intro r R hR
   change (V.ND.state r).map (fun B=>B.z8 V.NV V.MF)=some R at hR
   obtain ⟨B,hB,hBR⟩:= Option.map_eq_some_iff.mp hR
   rw [←hBR,B.fA]
   exact hBackSize r B (hV.tS B hB)
 exact hT.oP size hIncludeSize hBudgetV
lemma jV.EK {S T: tI G M ell} {A: ℕ} (L: ℕ)
   (h: jV L S T) (hA: 2≤ A)
   (hSize:∀r R,S.ND.state r=some R→ R.tree.vertices.card≤ A) (hHold: S.ND.Lm L)
   (hBudget: S.Nm.card≤ 2*(A+L*ell)*S.found.card): T.Nm.card≤ 2*(A+L*ell)*T.found.card:= by
 obtain ⟨U,O,hBundle,hExtra⟩:= h
 obtain ⟨Oe,Oc,V,W,hExt,hCheck,hU⟩:= hBundle
 have hAfter: fZ L V T:=⟨Oc,W,O,hCheck,by simpa only [←hU] using hExtra⟩
 have hVBudget:= hExt.gD hA hSize hHold hBudget
 have hVSize:= hExt.p5 hA hSize hHold
 exact hAfter.EK (A+L*ell) hVSize hVBudget
lemma bN (states: ℕ→ tI G M ell) (L: ℕ)
   (hstep:∀t,jV L (states t) (states (t+1)))
   (hSize0:∀r R,(states 0).ND.state r=some R→ R.tree.vertices.card≤ 2)
   (hHold0:(states 0).ND.Lm L) (hRemoved0:(states 0).Nm=∅):
   ∀T,(states T).Nm.card≤ 2*(2+T*(L*ell))*(states T).found.card:= by
 have hSizes:=bP states L hstep hSize0 hHold0
 have hHolds:∀t,(states t).ND.Lm L:= by
   intro t
   cases t with
   | zero => exact hHold0
   | succ t => exact (hstep t).Ks L
 intro T
 induction T with
 | zero => rw [hRemoved0,card_empty];omega
 | succ T ih =>
   have hBudgetS:(states T).Nm.card≤ 2*((2+T*(L*ell))+L*ell)*(states T).found.card:=
     ih.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (Nat.le_add_right _ _)))
   have hBudgetT:=(hstep T).EK L (by omega) (hSizes T) (hHolds T) hBudgetS
   convert hBudgetT using 1<;> ring
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma aC (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1))) (r: Fin N)
   (hNo: r∉(states 0).ND.IS) (T: ℕ) (Q: Lp G M r)
   (hQ:(states T).ND.state r=some Q):
   ∃B,(states 0).ND.state r=some B∧ Q.tree.vertices ⊆B.tree.vertices:= by
 have hAnti: Antitone (fun t=>(states t).ND.IS):=
   antitone_nat_of_succ_le (fun t=>(hstep t).qP limit)
 induction T generalizing Q with
 | zero => exact ⟨Q,hQ,subset_refl _⟩
 | succ T ih =>
   have hNoT: r∉(states T).ND.IS:= fun ha=>hNo (hAnti (Nat.zero_le T) ha)
   obtain ⟨C,hC,hQC⟩:=(hstep T).c1 limit hNoT Q hQ
   obtain ⟨B,hB,hCB⟩:= ih C hC
   exact ⟨B,hB,hQC.trans hCB⟩
lemma cU (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1))) (r: Fin N)
   (hActive: r∈(states 0).ND.IS) (T: ℕ)
   (hAlive: r∉(states T).Nm) (hLost: r∉(states T).ND.IS):
   ∃t,t<T∧ cO limit (states t) (states (t+1)) r∧ r∉(states (t+1)).ND.IS:= by
 induction T with
 | zero => exact (hLost hActive).elim
 | succ T ih =>
   by_cases hPrev: r∈(states T).ND.IS
   · exact ⟨T,by omega,(hstep T).CH limit r hAlive hPrev hLost,hLost⟩
   · have hAliveT: r∉(states T).Nm:= fun hr=>hAlive ((hstep T).In limit hr)
     obtain ⟨t,ht,hFrame,hNo⟩:= ih hAliveT hPrev
     exact ⟨t,by omega,hFrame,hNo⟩
lemma cO.zW {S T: tI G M ell} {limit: ℕ} {r: Fin N}
   (h: cO limit S T r) (hInternal: S.zA)
   (Z: v9 G M r) (hBound: Z.length≤ell)
   (hLive:∀j,j<2*Z.length→ T.NV.Adj (Z.vertex j) (Z.vertex (j+1)))
   (Q: Lp G M r) (hQ: T.ND.state r=some Q) (hVertices: Z.support⊆Q.tree.vertices):
   ∀i,i<Z.length→ T.labels (Z.KA i)≤ i+1:= by
 obtain ⟨O,U,R,P,hPass,hR,hP,hLen,hHeld,hMod,hSuffix⟩:= h
 change (U.ND.state r).map (fun A=>A.rC limit)=some R at hR
 obtain ⟨A,hA,hAR⟩:= Option.map_eq_some_iff.mp hR
 rw [←hAR] at hP hHeld hMod
 change A.active=some P at hP
 change A.modified=false at hMod
 have hAHeld: A.NU=false:= by
   change (A.NU|| decide (limit≤A.tree.vertices.card))=false at hHeld
   cases hh:A.NU<;> simp_all
 obtain ⟨B,hB,hQB⟩:= hSuffix.vT Q hQ
 have hBA: B=A:= Option.some.inj (hB.symm.trans hA)
 subst B
 have hInsideVertices: Z.support⊆A.tree.vertices:= by rw [←hQB];exact hVertices
 have hLiveU:∀j,j<2*Z.length→ U.NV.Adj (Z.vertex j) (Z.vertex (j+1)):=
   fun j hj=>hSuffix.MF (hLive j hj)
 have hInside:= hPass.h9 (tI.zA.IX S hInternal limit) A hA hMod Z hInsideVertices hLiveU
 have hExt: P.M4 Z:= by
   refine ⟨by omega,?_⟩
   intro j hj
   have hj0: j=0:= by omega
   rw [hj0,Z.first,P.first]
 have hLabels:= hPass.dP limit O A hA hMod hAHeld P Z hP hExt hBound
   (fun j hj=>hInside j (by omega)) (fun j hj=>hLiveU (2*j) (by omega))
 intro i hi
 exact (hSuffix.Jj _).trans (hLabels i hi)
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma aI (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1)))
   (hInternal:∀t,(states t).zA) (r: Fin N)
   (hInitial: r∈(states 0).ND.IS) (T: ℕ)
   (hAlive: r∉(states T).Nm) (hInactive: r∉(states T).ND.IS)
   (Q: Lp G M r) (hQ:(states T).ND.state r=some Q)
   (Z: v9 G M r) (hBound: Z.length≤ell)
   (hLive:∀j,j<2*Z.length→(states T).NV.Adj (Z.vertex j) (Z.vertex (j+1)))
   (hVertices: Z.support⊆Q.tree.vertices):
   ∀i,i<Z.length→(states T).labels (Z.KA i)≤ i+1:= by
 obtain ⟨t,ht,hFrame,hNo⟩:= cU states limit hstep r hInitial T hAlive hInactive
 let shifted (u: ℕ):= states (t+1+u)
 have hShift:∀u,jV limit (shifted u) (shifted (u+1)):= by
   intro u
   simpa only [shifted,Nat.add_assoc] using hstep (t+1+u)
 let L:= T-(t+1)
 have hEnd: shifted L=states T:= by dsimp [shifted,L];congr 1;omega
 have hQEnd:(shifted L).ND.state r=some Q:= by rw [hEnd];exact hQ
 obtain ⟨B,hB,hQB⟩:= aC shifted limit hShift r hNo L Q hQEnd
 have hAntiLive: Antitone (fun t=>(states t).NV):= antitone_nat_of_succ_le (fun t=>(hstep t).MF limit)
 have hAntiLabels (e: Fin N ×Fin N): Antitone (fun t=>(states t).labels e):=
   antitone_nat_of_succ_le (fun t=>(hstep t).Jj limit e)
 have hLiveLocal:∀j,j<2*Z.length→(states (t+1)).NV.Adj (Z.vertex j) (Z.vertex (j+1)):=
   fun j hj=>hAntiLive (by omega: t+1≤T) (hLive j hj)
 have hLocal:= hFrame.zW (hInternal t) Z hBound hLiveLocal B hB (hVertices.trans hQB)
 intro i hi
 exact (hAntiLabels (Z.KA i) (by omega: t+1≤T)).trans (hLocal i hi)
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma cO.Em {S T: tI G M ell} {limit: ℕ} {r: Fin N}
   (h: cO limit S T r) (hell: 1≤ell) (b: Fin N ×Fin N)
   (hM: M.Adj b.1 b.2) (hEdge: T.NV.Adj r b.1): T.labels b≤1:= by
 obtain ⟨O,U,R,P,hPass,hR,hP,hLen,hHeld,hMod,hSuffix⟩:= h
 change (U.ND.state r).map (fun A=>A.rC limit)=some R at hR
 obtain ⟨A,hA,hAR⟩:= Option.map_eq_some_iff.mp hR
 rw [←hAR] at hP hHeld hMod
 change A.active=some P at hP
 change A.modified=false at hMod
 have hAHeld: A.NU=false:= by
   change (A.NU|| decide (limit≤A.tree.vertices.card))=false at hHeld
   cases hh:A.NU<;> simp_all
 by_contra hn
 have hHead: P.vertex (2*P.length)=r:= by rw [hLen];exact P.first
 have hBridge: U.NV.Adj (P.vertex (2*P.length)) b.1:= by rw [hHead];exact hSuffix.MF hEdge
 have hUnmatched:¬M.Adj (P.vertex (2*P.length)) b.1:= by rw [hHead];exact P.L9 _
 have hHigh: P.length+1<U.labels b:= by have hm:=hSuffix.Jj b;omega
 obtain ⟨j,hj,he⟩:= hPass.cQ limit O A hA hMod hAHeld P hP b hM hBridge hUnmatched
   (by omega) hHigh
 omega
lemma aL (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1))) (r: Fin N)
   (hInitial: r∈(states 0).ND.IS) (T: ℕ)
   (hAlive: r∉(states T).Nm) (hInactive: r∉(states T).ND.IS)
   (hell: 1≤ell) (b: Fin N ×Fin N) (hM: M.Adj b.1 b.2)
   (hEdge:(states T).NV.Adj r b.1):(states T).labels b≤1:= by
 obtain ⟨t,ht,hFrame,hNo⟩:= cU states limit hstep r hInitial T hAlive hInactive
 have hAntiLive: Antitone (fun t=>(states t).NV):= antitone_nat_of_succ_le (fun t=>(hstep t).MF limit)
 have hAntiLabel: Antitone (fun t=>(states t).labels b):= antitone_nat_of_succ_le (fun t=>(hstep t).Jj limit b)
 exact (hAntiLabel (by omega: t+1≤T)).trans
   (hFrame.Em hell b hM (hAntiLive (by omega: t+1≤T) hEdge))
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma aT (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1)))
   (hInternal:∀t,(states t).zA)
   (hzero:∀e,(states 0).labels e=ell+1) (T: ℕ)
   (hJump:∀t,t<T→(states t).ND.M5 (states t).labels)
   (C: C9 G M) (hC: 1<C.length) (k: ℕ) (hBound: k+C.length≤ell)
   (hLive:∀j,j<2*C.length-1→(states T).NV.Adj (C.vertex j) (C.vertex (j+1)))
   (hHigh: k+C.length<(states T).labels (C.KA (C.length-1)))
   (hLabel:∀j,j+1<C.length→(states T).labels (C.KA j)≤k+j+1)
   (hInactive:∀j,j+1<C.length→¬(states T).ND.Lh (C.KA j)):
   (∀j,j+1<C.length→(states T).ND.IP (C.KA j))∧
   (states T).ND.M7 (C.KA (C.length-1)).swap:= by
 obtain ⟨tau,htau,htT,hSettled,hTarget,hActive⟩:=
   aK states limit hstep hInternal hzero T hJump C hC k hBound hLive hHigh hLabel hInactive
 constructor
 · intro j hj
   exact a0 states limit hstep tau T htT.le (C.KA j) (hSettled j hj)
     (C.D8 (states T) hLive j (by omega)).1
 · exact aZ states limit hstep tau T htT.le _ hTarget
     (C.D8 (states T) hLive (C.length-1) (by have hp:=C.positive;omega)).2
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma a5 (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1)))
   (hInternal:∀t,(states t).zA) (hzero:∀e,(states 0).labels e=ell+1)
   (T: ℕ) (hPast:∀t,t<T→(states t).ND.M5 (states t).labels)
   {r: Fin N} (Z: v9 G M r) (hBound: Z.length≤ell)
   (hInitial: r∈(states 0).ND.IS) (hInactiveRoot: r∉(states T).ND.IS)
   (hAlive: r∉(states T).Nm)
   (hLive:∀j,j<2*Z.length→(states T).NV.Adj (Z.vertex j) (Z.vertex (j+1)))
   (hInactive:∀j,j<Z.length→¬(states T).ND.Lh (Z.KA j)):
   ∀i,i<Z.length→(states T).labels (Z.KA i)≤ i+1:= by
 have hT: 0<T:= by
   by_contra hn
   have he: T=0:= by omega
   rw [he] at hInactiveRoot
   exact hInactiveRoot hInitial
 have hNo:= aR states limit hstep T hT
 intro i
 induction i using Nat.strong_induction_on with
 | h i ih =>
   intro hi
   by_cases hi0: i=0
   · subst i
     have hEdge:(states T).NV.Adj r (Z.KA 0).1:= by
       change (states T).NV.Adj r (Z.vertex 1)
       simpa only [Z.first] using hLive 0 (by omega)
     exact aL states limit hstep r hInitial T hAlive hInactiveRoot (by omega)
       (Z.KA 0) (Z.HR 0 hi) hEdge
   · by_contra hn
     let P:= Z.take (i+1) (by omega)
     have hP: 1<P.length:= by change 1< i+1;omega
     let C:= P.F8 0 (by omega)
     have hCLen: C.length=i+1:= rfl
     have hArc (j: ℕ): C.KA j=Z.KA j:= by rw [P.xI,Nat.zero_add];rfl
     have hLiveP:∀j,j<2*P.length→(states T).NV.Adj (P.vertex j) (P.vertex (j+1)):=
       fun j hj=>hLive j (by change j<2*(i+1) at hj;omega)
     have hLiveC:= P.uQ 0 (by omega) (states T).NV hLiveP
     have hHigh: 0+C.length<(states T).labels (C.KA (C.length-1)):= by
       rw [hCLen,Nat.add_sub_cancel,hArc]
       omega
     have hLabel:∀j,j+1<C.length→(states T).labels (C.KA j)≤0+j+1:= by
       intro j hj
       rw [hArc]
       simpa only [Nat.zero_add] using ih j (by omega) (by omega)
     have hInactiveC:∀j,j+1<C.length→¬(states T).ND.Lh (C.KA j):= by
       intro j hj
       rw [hArc]
       exact hInactive j (by omega)
     have hData:= aT states limit hstep hInternal hzero T hPast C (by omega) 0
       (by change 0+(i+1)≤ell;omega) hLiveC hHigh hLabel hInactiveC
     have hSettledP:∀j,j+1<P.length→(states T).ND.IP (P.KA j):= by
       intro j hj
       have hh:= hData.1 j (by change j+1< i+1;exact hj)
       rw [P.xI,Nat.zero_add] at hh
       exact hh
     have hLastP:(states T).ND.M7 (P.KA (P.length-1)).swap:= by
       have hh:=hData.2
       rwa [P.uP] at hh
     obtain ⟨A,hA,hInside⟩:=(states T).bI (hInternal T) hNo P hP hLiveP hSettledP hLastP
     have hLabels:= aI states limit hstep hInternal r hInitial T hAlive hInactiveRoot
       A hA P (by change i+1≤ell;omega) hLiveP hInside
     have hh:= hLabels i (by change i< i+1;omega)
     change (states T).labels (Z.KA i)≤ i+1 at hh
     exact hn hh
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma aH (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV limit (states t) (states (t+1)))
   (hInternal:∀t,(states t).zA) (hzero:∀e,(states 0).labels e=ell+1)
   (hJump0:(states 0).ND.M5 (states 0).labels)
   (hRoots0:∀r,(∀w,¬M.Adj r w)→ r∈(states 0).ND.IS)
   (T: ℕ) (P: C3 G M) (hLength: P.length≤ell)
   (hLive:∀j,j≤2*P.length→(states T).NV.Adj (P.vertex j) (P.vertex (j+1))):
   (P.support∩(states T).ND.Fo).Nonempty:= by
 have hInitial:= hRoots0 (P.vertex 0) P.Ki
 by_cases hT: T=0
 · subst T
   exact ⟨P.vertex 0,mem_inter.mpr ⟨P.mem_support 0 (by omega),(states 0).ND.lJ _ hInitial⟩⟩
 · by_contra hn
   have hAvoid:∀v∈P.support,v∉(states T).ND.Fo:= by
     intro v hv ha
     exact hn ⟨v,mem_inter.mpr ⟨hv,ha⟩⟩
   have hInactiveRoot: P.vertex 0∉(states T).ND.IS:= by
     intro ha
     exact hAvoid _ (P.mem_support 0 (by omega)) ((states T).ND.lJ _ ha)
   have hInactive:∀j,j<P.F1.length→¬(states T).ND.Lh (P.F1.KA j):= by
     intro j hj ha
     exact hAvoid _ (P.mem_support (2*j+1) (by change j<P.length at hj;omega))
       ((states T).ND.tJ _ ha)
   have hAlive: P.vertex 0∉(states T).Nm:=(states T).HK _ _ (hLive 0 (by omega))|>.1
   have hLivePrefix:∀j,j<2*P.F1.length→
       (states T).NV.Adj (P.F1.vertex j) (P.F1.vertex (j+1)):= fun j hj=>hLive j (by exact hj.le)
   have hPast:∀t,t<T→(states t).ND.M5 (states t).labels:=
     fun t _=>aS states limit hstep hInternal hzero hJump0 t
   have hLabels:= a5 states limit hstep hInternal hzero T hPast P.F1 hLength
     hInitial hInactiveRoot hAlive hLivePrefix hInactive
   have hReached:∀j,j<P.length→(states T).ND.M7 (P.F1.KA j):= by
     intro j hj
     have hLabel:= hLabels j hj
     have hArcAlive:=((states T).HK _ _ (hLive (2*j+1) (by omega))).1
     exact bM states limit hstep hzero T (P.F1.KA j)
       (hLabel.trans (by omega)) hArcAlive
   exact (states T).b2 (hInternal T)
     (aR states limit hstep T (by omega)) P hLive hReached
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma tI.mZ (hM: Matching G M) (r: Fin N)
   (R: Lp G M r) (hR:(tI.initial G M hM ell).ND.state r=some R): R.tree.vertices.card=1:= by
 change (if h:∀w,¬M.Adj r w then some (Lp.initial G M r h) else none)=some R at hR
 split_ifs at hR with hf
 cases Option.some.inj hR
 simp [Lp.initial,Bi.initial,Bi.vertices]
lemma tI.uE (hM: Matching G M) (L: ℕ) (hL: 2≤ L):
   (tI.initial G M hM ell).ND.Lm L:= by
 intro r R hR hLarge
 have hCard:=tI.mZ hM r R hR
 omega
lemma tI.gH (hM: Matching G M) (r: Fin N)
   (hFree:∀w,¬M.Adj r w): r∈(tI.initial G M hM ell).ND.IS:= by
 apply ((tI.initial G M hM ell).ND.xO _ r).mpr
 refine ⟨Lp.initial G M r hFree,?_,rfl⟩
 change (if h:∀w,¬M.Adj r w then some (Lp.initial G M r h) else none)=some (Lp.initial G M r hFree)
 rw [dif_pos hFree]
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma bF (states: ℕ→ tI G M ell) (L: ℕ)
   (hStep:∀t,jV L (states t) (states (t+1)))
   (hInternal:∀t,(states t).zA) (hZero:∀e,(states 0).labels e=ell+1)
   (hJump0:(states 0).ND.M5 (states 0).labels)
   (hRoots0:∀r,(∀w,¬M.Adj r w)→ r∈(states 0).ND.IS)
   (T: ℕ) (D: Finset (Fin N))
   (hLive:∀u v,G.Adj u v→ u∉(states T).Nm→ v∉(states T).Nm→
     u∉D→ v∉D→(states T).NV.Adj u v)
   (P: C3 G M) (hLength: P.length≤ ell):
   (P.support∩((states T).Nm∪(states T).ND.Fo∪D)).Nonempty:= by
 by_cases hRemoved:(P.support∩(states T).Nm).Nonempty
 · obtain ⟨v,hv⟩:=hRemoved
   exact ⟨v,mem_inter.mpr ⟨(mem_inter.mp hv).1,mem_union_left _ (mem_union_left _ (mem_inter.mp hv).2)⟩⟩
 by_cases hD:(P.support∩D).Nonempty
 · obtain ⟨v,hv⟩:=hD
   exact ⟨v,mem_inter.mpr ⟨(mem_inter.mp hv).1,mem_union_right _ (mem_inter.mp hv).2⟩⟩
 have hAlive:∀v∈P.support,v∉(states T).Nm:=
   fun v hv h=>hRemoved ⟨v,mem_inter.mpr ⟨hv,h⟩⟩
 have hGood:∀v∈P.support,v∉D:= fun v hv h=>hD ⟨v,mem_inter.mpr ⟨hv,h⟩⟩
 have hPLive:∀i,i≤ 2*P.length→(states T).NV.Adj (P.vertex i) (P.vertex (i+1)):= by
   intro i hi
   have hI:=P.mem_support i (by omega)
   have hJ:=P.mem_support (i+1) (by omega)
   exact hLive _ _ (P.Mu i hi) (hAlive _ hI) (hAlive _ hJ) (hGood _ hI) (hGood _ hJ)
 obtain ⟨v,hv⟩:=aH states L hStep hInternal hZero hJump0 hRoots0 T P hLength hPLive
 exact ⟨v,mem_inter.mpr ⟨(mem_inter.mp hv).1,mem_union_left _ (mem_union_right _ (mem_inter.mp hv).2)⟩⟩
lemma cT (states: ℕ→ tI G M ell) (hM: Matching G M)
   (hInitial: states 0=tI.initial G M hM ell) (L: ℕ) (hL: 2≤ L)
   (hStep:∀t,jV L (states t) (states (t+1)))
   (T: ℕ) (D: Finset (Fin N)) (hOmission:(states 0).Fh (states T) D)
   (F: Finset (C3 G M))
   (hDisjoint: Set.Pairwise (F: Set (C3 G M)) (fun P Q=>Disjoint P.support Q.support))
   (hShort:∀P∈F,P.length≤ ell):
   F.card≤ 2*(2+T*(L*ell))*(states T).found.card+
     (2*ell+1)*(states T).ND.IS.card+D.card:= by
 have hInternal0:(states 0).zA:= by rw [hInitial];exact tI.fB G M hM ell
 have hInternal:=aE states L hStep hInternal0
 have hZero:∀e,(states 0).labels e=ell+1:= by rw [hInitial];intro e;rfl
 have hJump0:(states 0).ND.M5 (states 0).labels:= by rw [hInitial];exact tI.BQ hM
 have hRoots0:∀r,(∀w,¬M.Adj r w)→ r∈(states 0).ND.IS:= by
   rw [hInitial];exact tI.gH hM
 have hSize0:∀r R,(states 0).ND.state r=some R→ R.tree.vertices.card≤ 2:= by
   rw [hInitial]
   intro r R hR
   have h:=tI.mZ hM r R hR
   omega
 have hHold0:(states 0).ND.Lm L:= by rw [hInitial];exact tI.uE hM L hL
 have hRemoved0:(states 0).Nm=∅:= by rw [hInitial];rfl
 have hRemoved:=bN states L hStep hSize0 hHold0 hRemoved0 T
 have hActive:=(states T).ND.f0 ell (states T).labels (states T).labelled
 have hLive:∀u v,G.Adj u v→ u∉(states T).Nm→ v∉(states T).Nm→
     u∉D→ v∉D→(states T).NV.Adj u v:= by
   intro u v hG
   apply hOmission u v
   rw [hInitial]
   exact hG
 have hHit:∀P∈F,(P.support∩((states T).Nm∪(states T).ND.Fo∪D)).Nonempty:=
   fun P hP=>bF states L hStep hInternal hZero hJump0 hRoots0 T D hLive P (hShort P hP)
 have hCard:=wT F C3.support _ hDisjoint hHit
 have hUnion:=(card_union_le ((states T).Nm∪(states T).ND.Fo) D).trans
   (Nat.add_le_add_right (card_union_le _ _) D.card)
 omega
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma tI.DY (G M: SimpleGraph (Fin N)) (hM: Matching G M) (ell: ℕ):
   (tI.initial G M hM ell).ND.height= 0:= by
 apply sum_eq_zero
 intro r hr
 change (if h:∀w,¬M.Adj r w then some (Lp.initial G M r h) else none).elim 0 Lp.height= 0
 split_ifs<;> rfl
end Be
end
noncomputable section
namespace Be
def Fn (ell: ℕ): ℕ:= 2*ell*(ell+2)*(2*ell+1)
def Ey (ell: ℕ): ℕ:= 16*Fn ell
def AG (ell: ℕ): ℕ:= 16*ell*(ell+1)*Fn ell
lemma wG {ell: ℕ} (hell: 0< ell): 0< Fn ell:= by
 unfold Fn
 positivity
lemma b5 (ell B a m: ℕ) (hell: 0< ell) (hB: 0< B)
   (h: a*(16*ell*(ell+1)*B)*(16*B)≤
     4*m*(16*ell*(ell+1)*B)+4*ell*(ell+1)*m*(16*B)): 2*B*a≤ m:= by
 have hk: 0< ell*(ell+1)*(16*B):= by positivity
 have hf:(a*(16*B))*(ell*(ell+1)*(16*B))≤(8*m)*(ell*(ell+1)*(16*B)):= by
   convert h using 1<;> ring
 have hc: a*(16*B)≤ 8*m:=(mul_le_mul_iff_left₀ hk).mp hf
 nlinarith
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   {S T: tI G M ell}
lemma qG.qM (limit: ℕ) (h: qG (limit+1) S T):
   T.ND.IS.card*limit≤ 4*matchingSize M+
     (2*(S.LN-T.LN)+(S.G1-T.G1))*limit:= by
 obtain ⟨O,K,U,V,hU,hV,rfl⟩:= h
 let H:= U.rC (limit+1)
 obtain ⟨U0,hU0,hPrune⟩:=hU.Np
 have hheld0:=S.eE U0 limit O.edges hU0
 have hheld:(U.rC (limit+1)).ND.LI.card*limit≤ 4*matchingSize M:= by
   cases hPrune
   exact hheld0
 have hmod:= hU.gC S U (limit+1) O.edges
 have hmodH: H.ND.Gc.card= U.ND.Gc.card:= congrArg Finset.card (U.cD _)
 have hsub: V.z9.ND.IS ⊆H.Dk.ND.IS:=
   (Bf.includeEdges V).qP.trans hV.qP
 have hcount:=(card_le_card hsub).trans H.jZ
 have hUwork:= hU.Ml
 rw [S.A9] at hUwork
 have hVwork:= hV.Ml
 change V.G1≤ H.Dk.G1 at hVwork
 have hback:= H.E7
 have hHwork: H.G1= U.G1:= U.iC _
 have hVout: V.z9.G1= V.G1:= V.n7
 have hcredit: H.ND.Fw≤ S.G1-V.z9.G1:= by
   rw [hVout]
   omega
 have hUrank:=(S.IX (limit+1)).rank_mono U hU.Jj
 have hVrank:= H.Dk.rank_mono V hV.Jj
 change U.LN≤ S.LN at hUrank
 change V.LN≤ U.LN at hVrank
 have hrank: S.LN-U.LN≤ S.LN-V.z9.LN:= by
   change S.LN-U.LN≤ S.LN-V.LN
   omega
 have hm: H.ND.Gc.card≤ 2*(S.LN-V.z9.LN):= by omega
 have hcountmul:= Nat.mul_le_mul_right limit hcount
 have hmodmul:= Nat.mul_le_mul_right limit hm
 have hcreditmul:= Nat.mul_le_mul_right limit hcredit
 nlinarith
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
variable {S T: tI G M ell}
lemma jV.qM (limit: ℕ) (h: jV (limit+1) S T):
   T.ND.IS.card*limit≤ 4*FasterDistributedMatching.ApproximateMatching.matchingSize M+
     (2*(S.LN-T.LN)+(S.G1-T.G1))*limit:= by
 obtain ⟨U,O,hU,hT⟩:= h
 have hbase:= hU.qM limit
 have hactive:= card_le_card hT.qP
 have hrank:= U.rank_mono T hT.Jj
 have hwork:= hT.Ml
 have hcredit: 2*(S.LN-U.LN)+(S.G1-U.G1)≤
     2*(S.LN-T.LN)+(S.G1-T.G1):= by omega
 exact (Nat.mul_le_mul_right limit hactive).trans
   (hbase.trans (Nat.add_le_add_left (Nat.mul_le_mul_right limit hcredit) _))
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
lemma aM (states: ℕ→ tI G M ell) (limit: ℕ)
   (hstep:∀t,jV (limit+1) (states t) (states (t+1))) (T: ℕ):
   (states T).ND.IS.card*T*limit≤ 4*matchingSize M*T+
     (2*(states 0).LN+(states 0).G1)*limit:= by
 let ranks (t: ℕ):=(states t).LN
 let NY (t: ℕ):=(states t).G1
 have hrank (t: ℕ): ranks (t+1)≤ ranks t:=(hstep t).rank_mono (limit+1)
 have hwork (t: ℕ): NY (t+1)≤ NY t:=(hstep t).Ml (limit+1)
 have hr:= zG ranks (fun t=> ranks t-ranks (t+1)) (fun t=> by have h:=hrank t;omega) T
 have hw:= zG NY (fun t=> NY t-NY (t+1)) (fun t=> by have h:=hwork t;omega) T
 have hr':(∑t∈ range T,(ranks t-ranks (t+1)))≤ ranks 0:= by omega
 have hw':(∑t∈ range T,(NY t-NY (t+1)))≤ NY 0:= by omega
 have ha: Antitone (fun t=>(states t).ND.IS.card):=
   antitone_nat_of_succ_le (fun t=> card_le_card ((hstep t).qP (limit+1)))
 have hone (t: ℕ) (ht: t∈ range T):
     (states T).ND.IS.card*limit≤ 4*matchingSize M+
       (2*(ranks t-ranks (t+1))+(NY t-NY (t+1)))*limit:= by
   have hcount:= ha (show t+1≤ T by have h:=mem_range.mp ht;omega)
   exact (Nat.mul_le_mul_right limit hcount).trans ((hstep t).qM limit)
 have hs:= sum_le_sum hone
 have hleft:(∑_∈ range T,(states T).ND.IS.card*limit)=
     (states T).ND.IS.card*T*limit:= by simp [mul_comm,mul_left_comm,mul_assoc]
 have hright:(∑t∈ range T,(4*matchingSize M+
     (2*(ranks t-ranks (t+1))+(NY t-NY (t+1)))*limit))=
     4*matchingSize M*T+(2*(∑t∈ range T,(ranks t-ranks (t+1)))+
       (∑t∈ range T,(NY t-NY (t+1))))*limit:= by
   simp_rw [add_mul]
   simp only [sum_add_distrib,←sum_mul,←mul_sum,sum_const,card_range,smul_eq_mul]
   ring
 rw [hleft,hright] at hs
 have hsum: 2*(∑t∈ range T,(ranks t-ranks (t+1)))+(∑t∈ range T,(NY t-NY (t+1)))≤
     2*ranks 0+NY 0:= by omega
 exact hs.trans (Nat.add_le_add_left (Nat.mul_le_mul_right limit hsum) _)
lemma aD (states: ℕ→ tI G M ell) (hM: Matching G M)
   (hinitial: states 0= tI.initial G M hM ell) (limit: ℕ)
   (hstep:∀t,jV (limit+1) (states t) (states (t+1))) (T: ℕ):
   (states T).ND.IS.card*T*limit≤ 4*matchingSize M*T+4*ell*(ell+1)*matchingSize M*limit:= by
 have h:= aM states limit hstep T
 have hr:=(states 0).BU
 have hh:(states 0).ND.height= 0:= by rw [hinitial];exact tI.DY G M hM ell
 have hw:(states 0).G1= 2*ell*(states 0).LN:= by
   rw [tI.G1,hh,zero_add]
 rw [hw] at h
 have hbudget: 2*(states 0).LN+2*ell*(states 0).LN≤ 4*ell*(ell+1)*matchingSize M:= by
   nlinarith [Nat.mul_le_mul_left (2+2*ell) hr]
 exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right limit hbudget) _)
end Be
end
noncomputable section
namespace Be
lemma aJ {N: ℕ} {G M: SimpleGraph (Fin N)} {ell: ℕ}
   (states: ℕ→ tI G M ell) (hM: Matching G M)
   (hinitial: states 0= tI.initial G M hM ell) (hell: 0< ell)
   (hstep:∀t,jV (Ey ell+1) (states t) (states (t+1))):
   2*Fn ell*(states (AG ell)).ND.IS.card≤ matchingSize M:= by
 have h:= aD states hM hinitial (Ey ell) hstep (AG ell)
 apply b5 ell (Fn ell) _ (matchingSize M) hell (wG hell)
 exact h
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
lemma lR (hM: Matching G M) (F: Finset (C3 G M)) (k: ℕ)
   (hd: Set.Pairwise (F: Set (C3 G M)) (fun P Q=> Disjoint P.support Q.support))
   (hshort:∀P∈ F,P.length≤ k)
   (hmax:∀P: C3 G M,P.length≤ k→∃Q∈ F,¬Disjoint P.support Q.support)
   (hsmall: k*(k+2)*F.card≤ matchingSize M):
   k*optimum G≤(k+2)*matchingSize M:= by
 let D:= Gp F
 let a:=∑P∈ F,P.length
 let Y:= F.card
 let mr:= matchingSize (Dy M D)
 let or:= optimum (Dy G D)
 have hNo:= nA hM F k hmax
 have hResidual:= c8 (BF G M hM D) k hNo
 have hDelete:= k4 G D
 have hMsize:= sC hM F hd
 have hDsize:= u6 F hd
 have ha: a≤ k*Y:= by
   calc
     a≤∑_∈ F,k:= sum_le_sum hshort
     _= k*Y:= by simp [Y,mul_comm]
 have hupper: optimum G≤ or+2*a+2*Y:= by
   change optimum G≤ optimum (Dy G (Gp F))+(Gp F).card at hDelete
   rw [hDsize] at hDelete
   change optimum G≤ or+(2*a+2*Y) at hDelete
   omega
 have hmr: mr+a= matchingSize M:= hMsize
 have hres:(k+1)*or≤(k+2)*mr:= hResidual
 have hmrmul:= congrArg (fun n=>(k+2)*n) hmr
 have huppermul:= Nat.mul_le_mul_left (k+1) hupper
 have hprecise:(k+1)*optimum G≤(k+2)*matchingSize M+k*a+2*(k+1)*Y:= by
   nlinarith [hres,hmrmul,huppermul]
 have hprecisemul:= Nat.mul_le_mul_left k hprecise
 have hamul:= Nat.mul_le_mul_left (k*k) ha
 have hsmallmul:= Nat.mul_le_mul_left (k+2) hsmall
 have hcoef:(k*k*k+2*k*(k+1))*Y≤ k*(k+2)*(k+2)*Y:= by
   apply Nat.mul_le_mul_right Y
   nlinarith
 have hcombined:(k+1)*(k*optimum G)≤(k+1)*((k+2)*matchingSize M):= by
   change k*(k+2)*Y≤ matchingSize M at hsmall
   change (k+2)*(k*(k+2)*Y)≤(k+2)*matchingSize M at hsmallmul
   nlinarith [hprecisemul,hamul,hsmallmul,hcoef]
 exact Nat.le_of_mul_le_mul_left hcombined (by omega)
end Be
end
noncomputable section
namespace Be
variable {N: ℕ}
structure qL (G M: SimpleGraph (Fin N)) (k: ℕ) where
 paths: Finset (C3 G M)
 disjoint: Set.Pairwise (paths: Set (C3 G M)) (fun P Q=> Disjoint P.support Q.support)
 short:∀P∈ paths,P.length≤ k
namespace qL
variable {G M: SimpleGraph (Fin N)} {k: ℕ} (S: qL G M k)
def empty (G M: SimpleGraph (Fin N)) (k: ℕ): qL G M k where
 paths:=∅
 disjoint:= by intro P hP;simp at hP
 short:= by intro P hP;simp at hP
lemma card_le: S.paths.card≤ N:= by
 have hhit:∀P∈ S.paths,(P.support ∩(univ: Finset (Fin N))).Nonempty:= by
   intro P hP
   refine ⟨P.vertex 0,mem_inter.mpr ⟨?_,mem_univ _⟩⟩
   exact mem_image.mpr ⟨0,mem_range.mpr (by omega),rfl⟩
 have hh:= wT S.paths C3.support univ S.disjoint hhit
 simpa only [card_univ,Fintype.card_fin] using hh
lemma Ei (G M: SimpleGraph (Fin N)) (k: ℕ):
   ∃S: qL G M k,∀T: qL G M k,T.paths.card≤ S.paths.card:= by
 let F:=(range (N+1)).filter (fun n=>∃S: qL G M k,S.paths.card= n)
 have hF: F.Nonempty:=⟨0,mem_filter.mpr ⟨mem_range.mpr (by omega),empty G M k,rfl⟩⟩
 let n:= F.max' hF
 obtain ⟨S,hS⟩:=(mem_filter.mp (max'_mem F hF)).2
 refine ⟨S,?_⟩
 intro T
 rw [hS]
 exact le_max' F T.paths.card (mem_filter.mpr ⟨mem_range.mpr (by have h:=T.card_le;omega),T,rfl⟩)
lemma uR (hmax:∀T: qL G M k,T.paths.card≤ S.paths.card):
   ∀P: C3 G M,P.length≤ k→∃Q∈ S.paths,¬Disjoint P.support Q.support:= by
 intro P hPl
 by_contra hnone
 have hd:∀Q∈ S.paths,Disjoint P.support Q.support:= by
   intro Q hQ
   by_contra hn
   exact hnone ⟨Q,hQ,hn⟩
 have hnot: P∉ S.paths:= by
   intro hP
   have h0: P.vertex 0∈ P.support:= mem_image.mpr ⟨0,mem_range.mpr (by omega),rfl⟩
   exact disjoint_left.mp (hd P hP) h0 h0
 let T: qL G M k:=
   { paths:= insert P S.paths
     disjoint:= by
       intro Q hQ R hR hne
       rcases mem_insert.mp hQ with hQ|hQ
       · subst Q
         rcases mem_insert.mp hR with hR|hR
         · exact (hne hR.symm).elim
         · exact hd R hR
       · rcases mem_insert.mp hR with hR|hR
         · subst R
           exact (hd Q hQ).symm
         · exact S.disjoint hQ hR hne
     short:= by
       intro Q hQ
       rcases mem_insert.mp hQ with hQ|hQ
       · rw [hQ];exact hPl
       · exact S.short Q hQ}
 have hh:= hmax T
 change (insert P S.paths).card≤ S.paths.card at hh
 rw [card_insert_of_notMem hnot] at hh
 omega
end qL
lemma aU {G M: SimpleGraph (Fin N)} (hM: Matching G M) (k: ℕ)
   (hbad:(k+2)*matchingSize M< k*optimum G):
   ∃F: Finset (C3 G M),
     Set.Pairwise (F: Set (C3 G M)) (fun P Q=> Disjoint P.support Q.support)∧
     (∀P∈ F,P.length≤ k)∧
     (∀P: C3 G M,P.length≤ k→∃Q∈ F,¬Disjoint P.support Q.support)∧
     matchingSize M< k*(k+2)*F.card:= by
 obtain ⟨S,hS⟩:= qL.Ei G M k
 have hmax:= S.uR hS
 refine ⟨S.paths,S.disjoint,S.short,hmax,?_⟩
 by_contra hnot
 have hs: k*(k+2)*S.paths.card≤ matchingSize M:= by omega
 have hgood:= lR hM S.paths k S.disjoint S.short hmax hs
 omega
end Be
end
noncomputable section
namespace Be
lemma sG (m: ℕ→ ℕ) (opt k B R: ℕ) (hR: 0< R)
   (hmono: Monotone m) (hopt:∀t,m t≤ opt) (hinit: opt≤ B*m 0)
   (hphase:∀t,(k+2)*m t< k*opt→ m t≤ R*(m (t+1)-m t)):
   k*opt≤(k+2)*m (B*R):= by
 by_contra hbad
 have hbad':(k+2)*m (B*R)< k*opt:= by omega
 have hpos: 0< m 0:= by
   by_contra hh
   have he: m 0= 0:= by omega
   rw [he,mul_zero] at hinit
   have hopt0: opt= 0:= by omega
   rw [hopt0,mul_zero] at hbad'
   omega
 have hstep:∀t,t< B*R→ R*m t+m 0≤ R*m (t+1):= by
   intro t ht
   have hmt:= hmono (show t≤ B*R by omega)
   have hbad_t:(k+2)*m t< k*opt:= lt_of_le_of_lt (Nat.mul_le_mul_left _ hmt) hbad'
   have hp:= hphase t hbad_t
   have hzero:= hmono (Nat.zero_le t)
   have hs:= Nat.sub_add_cancel (hmono (Nat.le_succ t))
   nlinarith
 have hsum:∀t,t≤ B*R→ R*m 0+t*m 0≤ R*m t:= by
   intro t
   induction t with
   | zero => simp
   | succ t ih =>
     intro ht
     have hi:= ih (by omega)
     have hs:= hstep t (by omega)
     nlinarith
 have htotal:= hsum (B*R) le_rfl
 have hlast:= Nat.mul_le_mul_left R ((hopt (B*R)).trans hinit)
 have hp:= Nat.mul_pos hR hpos
 nlinarith
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
def zX (ell: ℕ): ℕ:= 2+AG ell*((Ey ell+1)*ell)
def cW (ell: ℕ): ℕ:= 4*ell*(ell+2)*zX ell
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {G M: SimpleGraph (Fin N)}
lemma fI (m k size found active ell pack bad: ℕ)
   (hLarge: m<k*(k+2)*pack)
   (hCharge: pack≤ 2*size*found+(2*ell+1)*active+bad)
   (hActive: 4*k*(k+2)*(2*ell+1)*active≤ m)
   (hBad: 4*k*(k+2)*bad≤ m): m<4*k*(k+2)*size*found:= by
 have hMult:=Nat.mul_le_mul_left (4*k*(k+2)) hCharge
 have hLarge':=Nat.mul_lt_mul_of_pos_left hLarge (by omega: 0<(4:ℕ))
 nlinarith
lemma oO {ell: ℕ} (states: ℕ→ tI G M ell) (hM: Matching G M)
   (hInitial: states 0=tI.initial G M hM ell) (hell: 0<ell)
   (hStep:∀t,jV (Ey ell+1) (states t) (states (t+1)))
   (D: Finset (Fin N))
   (hOmission:(states 0).Fh (states (AG ell)) D)
   (hSmall: 4*ell*(ell+2)*D.card≤ matchingSize M)
   (hBad:(ell+2)*matchingSize M<ell*optimum G):
   matchingSize M≤ cW ell*
     (matchingSize (states (AG ell)).Et-matchingSize M):= by
 obtain ⟨F,hDisjoint,hShort,hMax,hLarge⟩:=aU hM ell hBad
 have hInverse:=wG hell
 have hL: 2≤ Ey ell+1:= by unfold Ey;omega
 have hCharge:=cT states hM hInitial (Ey ell+1) hL hStep
   (AG ell) D hOmission F hDisjoint hShort
 change F.card≤ 2*zX ell*(states (AG ell)).found.card+
   (2*ell+1)*(states (AG ell)).ND.IS.card+D.card at hCharge
 have hActive:=aJ states hM hInitial hell hStep
 have hA: 4*ell*(ell+2)*(2*ell+1)*(states (AG ell)).ND.IS.card≤ matchingSize M:= by
   unfold Fn at hActive
   nlinarith
 have hGain:=fI (matchingSize M) ell (zX ell)
   (states (AG ell)).found.card (states (AG ell)).ND.IS.card
   ell F.card D.card hLarge hCharge hA hSmall
 rw [(states (AG ell)).Eu.2,Nat.add_sub_cancel_left]
 exact hGain.le
end Be
end
noncomputable section
namespace Be
variable {K: Type} {N ell size B P L: ℕ} {G M: SimpleGraph (Fin N)}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M}
   (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K) (hS: 2≤ size)
   (hOracle: qH A k G ids size B)
   (target: ℕ) (hTarget: 0<target) (hB: 0<B) (hOpt: optimum G≤ B*matchingSize M)
   (hFit: 2+P*(L*ell)≤ size) (hL: 2≤ L)
   (data0: Fin N→ Ln)
   (h0: Fi (tI.initial G M hOut.1 ell) ids hi out hOut data0)
def MP:(t: ℕ)→ Fj (ell:=ell) ids hi out hOut P L t
 | 0=>{
     state:=tI.initial G M hOut.1 ell
     data:=data0
     encoding:=fun _=>h0
     size:=by
       intro r V hV
       have hh:=tI.mZ hOut.1 r V hV
       simpa only [Nat.zero_mul,Nat.add_zero] using (show V.tree.vertices.card≤ 2 by omega)
     hold:=tI.uE hOut.1 L hL}
 | t+1=>(MP t).next A k hS hOracle target hTarget hB hOpt hFit
lemma Gt (t: ℕ) (ht: t≤P):
   (MP A k hS hOracle target hTarget hB hOpt hFit hL data0 h0 t).data=
     execute (IM.MR (fun i=>oQ A k size ell L
       ((MP A k hS hOracle target hTarget hB hOpt hFit hL data0 h0 i).MY A k hS hOracle target hTarget hB hOpt hFit).NP) t)
       G () ids data0:= by
 let run:=MP A k hS hOracle target hTarget hB hOpt hFit hL data0 h0
 let MR:=fun i=>oQ A k size ell L
   ((run i).MY A k hS hOracle target hTarget hB hOpt hFit).NP
 have hConfig:∀n≤P,(run n).data=IM.Dw MR G ids data0 n:=by
   intro n hn
   induction n with
   | zero => rfl
   | succ n ih =>
     have hN: n<P:=by omega
     have hh:=((run n).MY A k hS hOracle target hTarget hB hOpt hFit).Kf hN
     change (run (n+1)).data=execute (MR n) G () ids (run n).data at hh
     change (run (n+1)).data=execute (MR n) G () ids (IM.Dw MR G ids data0 n)
     exact hh.trans (congrArg (fun d=>execute (MR n) G () ids d) (ih (by omega)))
 change (run t).data=execute (IM.MR MR t) G () ids data0
 rw [hConfig t ht]
 funext v
 exact (IM.Gy MR G ids data0 t v).symm
end Be
end
noncomputable section
namespace Be
def AI (ell: ℕ): ℕ:=4*ell*(ell+2)*AG ell
def AH (ell B: ℕ): ℕ:=3*AI ell*(2*zX ell*B)*(2*ell+B)
variable {K: Type} {N ell B: ℕ} {G M: SimpleGraph (Fin N)}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids} {out: Fin N→ Option ℕ}
   {hOut: ReportsMatching G ids out M}
   (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   (hOracle: qH A k G ids (zX ell) B)
   (hB: 0<B) (hOpt: optimum G≤ B*matchingSize M) (hell: 0<ell)
   (data0: Fin N→ Ln)
   (h0: Fi (tI.initial G M hOut.1 ell) ids hi out hOut data0)
include hOracle hB hOpt hell h0 in
lemma nK:∃(NP: ℕ→ IJ) (T: tI G M ell),
   (∀i<AG ell,(NP i).1<AH ell B∧
     (NP i).2.1<AH ell B∧(NP i).2.2<AH ell B)∧
   Fi T ids hi out hOut
     (execute (IM.MR (fun i=>oQ A k (zX ell) ell
       (Ey ell+1) (NP i)) (AG ell)) G () ids data0)∧
   ((ell+2)*matchingSize M<ell*optimum G→
     matchingSize M≤ cW ell*(matchingSize T.Et-matchingSize M)):= by
 have hS: 2≤ zX ell:=by unfold zX;omega
 have hTarget: 0<AI ell:=by
   unfold AI AG Fn
   positivity
 have hL: 2≤ Ey ell+1:=by
   have hh:=wG hell
   unfold Ey
   omega
 let run:=MP A k hS hOracle (AI ell) hTarget hB hOpt (le_refl (zX ell)) hL data0 h0
 let NP:=fun i=>((run i).MY A k hS hOracle (AI ell) hTarget hB hOpt
   (le_refl (zX ell))).NP
 let states:=fun i=>(run i).state
 let omitted:=fun i=>((run i).MY A k hS hOracle (AI ell) hTarget hB hOpt
   (le_refl (zX ell))).omitted
 have hStep:∀i,jV (Ey ell+1) (states i) (states (i+1)):=by
   intro i
   exact ((run i).MY A k hS hOracle (AI ell) hTarget hB hOpt
     (le_refl (zX ell))).Ly
 have hCover:∀i,(states i).Fh (states (i+1)) (omitted i):=by
   intro i
   exact ((run i).MY A k hS hOracle (AI ell) hTarget hB hOpt
     (le_refl (zX ell))).cover
 let D:=(range (AG ell)).biUnion omitted
 have hUnion:(states 0).Fh (states (AG ell)) D:=
   pJ states omitted hCover (fun i=>(hStep i).In) (AG ell)
 have hSmall: 4*ell*(ell+2)*D.card≤ matchingSize M:=by
   apply eD D ((range (AG ell)).image omitted)
     (4*ell*(ell+2)) (AG ell) (matchingSize M)
   · intro v hv
     obtain ⟨i,hi,hV⟩:=mem_biUnion.mp hv
     exact mem_biUnion.mpr ⟨omitted i,mem_image.mpr ⟨i,hi,rfl⟩,hV⟩
   · exact (card_image_le).trans (card_range _).le
   · intro E hE
     obtain ⟨i,hi,hEq⟩:=mem_image.mp hE
     subst E
     exact ((run i).MY A k hS hOracle (AI ell) hTarget hB hOpt
       (le_refl (zX ell))).small (mem_range.mp hi)
 refine ⟨NP,states (AG ell),?_,?_,?_⟩
 · intro i hi
   exact ((run i).MY A k hS hOracle (AI ell) hTarget hB hOpt
     (le_refl (zX ell))).K9 hi
 · have hEncoding:=(run (AG ell)).encoding (le_refl _)
   have hData:=Gt A k hS hOracle (AI ell) hTarget hB hOpt
     (le_refl (zX ell)) hL data0 h0 (AG ell) (le_refl _)
   rw [hData] at hEncoding
   exact hEncoding
 · intro hBad
   exact oO states hOut.1 rfl hell hStep D hUnion hSmall hBad
end Be
end
noncomputable section
namespace Be
def Ln.report (z: Ln): Option ℕ:=if z.Nm then z.Md else z.Jf
def KJ {V: Type} (data: V→ Ln): V→ Option ℕ:=fun v=>(data v).report
variable {K: Type} {N ell B: ℕ} {G M: SimpleGraph (Fin N)}
   {ids: Fin N→ ℕ} {hi: Function.Injective ids}
   (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   (hOracle: qH A k G ids (zX ell) B)
   (hB: 0<B) (hOpt: optimum G≤ B*matchingSize M) (hell: 0<ell)
   (data: Fin N→ Ln) (hNei:∀v,(data v).neighbors=neighborIDs G ids v)
   (hOut: ReportsMatching G ids (KJ data) M)
include hi hOracle hB hOpt hell hNei hOut in
lemma vF:∃(NP: ℕ→ IJ) (M': SimpleGraph (Fin N)),
   (∀i<AG ell,(NP i).1<AH ell B∧
     (NP i).2.1<AH ell B∧(NP i).2.2<AH ell B)∧
   ReportsMatching G ids (KJ (execute (If A k (zX ell) ell
     (Ey ell+1) (AG ell) NP) G () ids data)) M'∧
   (∀v,(execute (If A k (zX ell) ell
     (Ey ell+1) (AG ell) NP) G () ids data v).neighbors=neighborIDs G ids v)∧
   matchingSize M≤ matchingSize M'∧
   ((ell+2)*matchingSize M<ell*optimum G→
     matchingSize M≤ cW ell*(matchingSize M'-matchingSize M)):= by
 let resetData:=execute (yJ ell) G () ids data
 have hReset: resetData=(fun v=>Ln.K8 ell (ids v) (neighborIDs G ids v) (KJ data v)):=by
   funext v
   change Ln.K8 ell (ids v) (data v).neighbors (KJ data v)=_
   rw [hNei v]
 have h0: Fi (tI.initial G M hOut.1 ell) ids hi (KJ data) hOut resetData:=by
   rw [hReset]
   exact gI G M ids hi (KJ data) hOut
 obtain ⟨NP,T,hStops,hEncoding,hGain⟩:=nK A k hOracle hB hOpt hell resetData h0
 have hData: execute (If A k (zX ell) ell (Ey ell+1)
     (AG ell) NP) G () ids data=
     execute (IM.MR (fun i=>oQ A k (zX ell) ell
       (Ey ell+1) (NP i)) (AG ell)) G () ids resetData:=AZ _ _ G ids data
 refine ⟨NP,T.Et,hStops,?_,?_,T.Cq,hGain⟩
 · rw [hData]
   exact hEncoding.output
 · intro v
   rw [hData]
   exact hEncoding.neighbors v
end Be
end
noncomputable section
namespace Be
structure s9 {N: ℕ} (G: SimpleGraph (Fin N)) (ids: Fin N→ ℕ) (m0: ℕ) where
 MG: SimpleGraph (Fin N)
 data: Fin N→ Ln
 Nn: ReportsMatching G ids (KJ data) MG
 neighbors:∀v,(data v).neighbors=neighborIDs G ids v
 lower: m0≤ matchingSize MG
namespace s9
variable {K: Type} {N ell B m0: ℕ} {G: SimpleGraph (Fin N)} {ids: Fin N→ ℕ}
   (hi: Function.Injective ids) (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   (hOracle: qH A k G ids (zX ell) B)
   (hB: 0<B) (hOpt: optimum G≤ B*m0) (hell: 0<ell)
   (X: s9 G ids m0)
structure Mt where
 next: s9 G ids m0
 NP: ℕ→ IJ
 K9:∀i<AG ell,(NP i).1<AH ell B∧
   (NP i).2.1<AH ell B∧(NP i).2.2<AH ell B
 Kf: next.data=execute (If A k (zX ell) ell
   (Ey ell+1) (AG ell) NP) G () ids X.data
 monotone: matchingSize X.MG≤ matchingSize next.MG
 NT:(ell+2)*matchingSize X.MG<ell*optimum G→
   matchingSize X.MG≤ cW ell*(matchingSize next.MG-matchingSize X.MG)
def MY: X.Mt (ell:=ell) (B:=B) A k:=Classical.choice (by
 have hApprox: optimum G≤ B*matchingSize X.MG:=hOpt.trans (Nat.mul_le_mul_left B X.lower)
 obtain ⟨NP,M',hStops,hReports,hNei,hMono,hGain⟩:=vF (hi:=hi)
   A k hOracle hB hApprox hell X.data X.neighbors X.Nn
 exact ⟨⟨⟨M',execute (If A k (zX ell) ell (Ey ell+1)
   (AG ell) NP) G () ids X.data,hReports,hNei,X.lower.trans hMono⟩,
   NP,hStops,rfl,hMono,hGain⟩⟩)
end s9
variable {K: Type} {N ell B: ℕ} {G M0: SimpleGraph (Fin N)} {ids: Fin N→ ℕ}
   (hi: Function.Injective ids) (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   (hOracle: qH A k G ids (zX ell) B)
   (hB: 0<B) (hOpt: optimum G≤ B*matchingSize M0) (hell: 0<ell)
   (data0: Fin N→ Ln) (hNei:∀v,(data0 v).neighbors=neighborIDs G ids v)
   (hReports: ReportsMatching G ids (KJ data0) M0)
def zI: ℕ→ s9 G ids (matchingSize M0)
 | 0=>⟨M0,data0,hReports,hNei,le_refl _⟩
 | t+1=>((zI t).MY hi A k hOracle hB hOpt hell).next
lemma l2 (t: ℕ):
   (zI hi A k hOracle hB hOpt hell data0 hNei hReports t).data=
     execute (IM.MR (fun i=>If A k (zX ell) ell
       (Ey ell+1) (AG ell)
       ((zI hi A k hOracle hB hOpt hell data0 hNei hReports i).MY hi A k hOracle hB hOpt hell).NP) t)
       G () ids data0:= by
 let run:=zI hi A k hOracle hB hOpt hell data0 hNei hReports
 let MR:=fun i=>If A k (zX ell) ell (Ey ell+1) (AG ell)
   ((run i).MY hi A k hOracle hB hOpt hell).NP
 have hConfig:∀n,(run n).data=IM.Dw MR G ids data0 n:=by
   intro n
   induction n with
   | zero => rfl
   | succ n ih =>
     have hh:=((run n).MY hi A k hOracle hB hOpt hell).Kf
     change (run (n+1)).data=execute (MR n) G () ids (run n).data at hh
     exact hh.trans (congrArg (fun d=>execute (MR n) G () ids d) ih)
 change (run t).data=execute (IM.MR MR t) G () ids data0
 rw [hConfig]
 funext v
 exact (IM.Gy MR G ids data0 t v).symm
lemma bJ:
   ell*optimum G≤(ell+2)*matchingSize
     (zI hi A k hOracle hB hOpt hell data0 hNei hReports
       (B*cW ell)).MG:= by
 let run:=zI hi A k hOracle hB hOpt hell data0 hNei hReports
 have hR: 0<cW ell:=by
   unfold cW zX
   positivity
 apply sG (fun t=>matchingSize (run t).MG) (optimum G) ell B
   (cW ell) hR
 · apply monotone_nat_of_le_succ
   intro t
   exact ((run t).MY hi A k hOracle hB hOpt hell).monotone
 · intro t
   exact qJ.gQ G (run t).MG (run t).Nn.1
 · exact hOpt
 · intro t
   exact ((run t).MY hi A k hOracle hB hOpt hell).NT
end Be
end
noncomputable section
namespace Be
def H4 (own: ℕ) (out: Option ℕ) (messages: Multiset (ℕ ×Option ℕ)): Option ℕ:=
 if ∃m∈messages,out=some m.1∧ m.2=some own then out else none
def CJ: Deterministic Unit (Option ℕ) (Option ℕ):=Fd.MN H4
variable {N: ℕ} (G: SimpleGraph (Fin N)) (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (out: Fin N→ Option ℕ)
def Js: SimpleGraph (Fin N) where
 Adj u v:=G.Adj u v∧ out u=some (ids v)∧ out v=some (ids u)
 symm:=⟨fun _ _ h=>⟨h.1.symm,h.2.2,h.2.1⟩⟩
 loopless:=⟨fun _ h=>h.1.ne rfl⟩
include hi in
lemma pG: Matching G (Js G ids out):=by
 apply tB.n4 G (Js G ids out) (fun _ _ h=>h.1)
 intro u v w hV hW
 exact hi (Option.some.inj (hV.2.1.symm.trans hW.2.1))
lemma lK (u: Fin N): execute CJ G () ids out u=
   if ∃v,(Js G ids out).Adj u v then out u else none:= by
 unfold execute CJ
 rw [Fd.Cn]
 unfold H4
 congr 1
 apply propext
 constructor
 · rintro ⟨m,hM,hOut,hOwn⟩
   obtain ⟨v,hV,hEq⟩:=Multiset.mem_map.mp hM
   subst m
   exact ⟨v,(G.mem_neighborFinset u v).mp hV,hOut,hOwn⟩
 · rintro ⟨v,hV,hOut,hOwn⟩
   exact ⟨(ids v,out v),Multiset.mem_map.mpr ⟨v,(G.mem_neighborFinset u v).mpr hV,rfl⟩,hOut,hOwn⟩
include hi in
lemma jJ: ReportsMatching G ids (execute CJ G () ids out) (Js G ids out):= by
 refine ⟨pG G ids hi out,?_⟩
 intro u
 rw [lK G ids out u]
 by_cases h:∃v,(Js G ids out).Adj u v
 · rw [if_pos h]
   obtain ⟨v,hV⟩:=h
   refine ⟨?_,?_⟩
   · constructor
     · intro hNone
       have hh: out u=some (ids v):=hV.2.1
       rw [hNone] at hh
       cases hh
     · intro hFree
       exact (hFree v hV).elim
   · intro j
     constructor
     · intro hJ
       exact ⟨v,hV,Option.some.inj (hV.2.1.symm.trans hJ)⟩
     · rintro ⟨w,hW,hJ⟩
       exact hW.2.1.trans (congrArg some hJ)
 · rw [if_neg h]
   refine ⟨⟨fun _ v hV=>h ⟨v,hV⟩,fun _=>rfl⟩,?_⟩
   intro j
   exact ⟨(fun hh=>by cases hh),fun ⟨v,hV,_⟩=>(h ⟨v,hV⟩).elim⟩
lemma fL (M: SimpleGraph (Fin N)) (hOut: ReportsMatching G ids out M):
   execute CJ G () ids out=out:= by
 funext u
 rw [lK G ids out u]
 cases hU: out u with
 | none => split_ifs<;> rfl
 | some j =>
   obtain ⟨v,hUV,hID⟩:=(hOut.2 u).2 j|>.mp hU
   have hV: out v=some (ids u):=(hOut.2 v).2 (ids u)|>.mpr ⟨u,hUV.symm,rfl⟩
   rw [if_pos ⟨v,hOut.1.1 hUV,hU.trans (congrArg some hID.symm),hV⟩]
end Be
end
noncomputable section
namespace Be
def KT (ell B: ℕ): ℕ:=B*cW ell
abbrev Bj (ell B: ℕ):=
 Fin (KT ell B)→ Fin (AG ell)→
   Fin (AH ell B) ×Fin (AH ell B) ×Fin (AH ell B)
def Kj (ell B: ℕ) (σ: Bj ell B) (t i: ℕ): IJ:=
 if ht: t<KT ell B then
   if hi: i<AG ell then
     let z:=σ ⟨t,ht⟩ ⟨i,hi⟩
     (z.1.val,z.2.1.val,z.2.2.val)
   else (0,0,0)
 else (0,0,0)
def I7 {K: Type} (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   (ell B: ℕ) (σ: Bj ell B): Deterministic Unit Ln Ln:=
 IM.MR (fun t=>If A k (zX ell) ell
   (Ey ell+1) (AG ell) (Kj ell B σ t)) (KT ell B)
def I6 {K: Type} (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   (ell B: ℕ) (σ: Bj ell B): Deterministic Unit Ln (Option ℕ):=
 Ff.sequence
   (C7.transform (I7 A k ell B σ) (fun _ z=>z) (fun _ _ z=>z.report))
   CJ (fun _ _ _ z=>z)
variable {K: Type} {N: ℕ} (G: SimpleGraph (Fin N)) (ids: Fin N→ ℕ) (hi: Function.Injective ids)
   (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K) (ell B: ℕ) (σ: Bj ell B)
   (data: Fin N→ Ln)
lemma t0: execute (I6 A k ell B σ) G () ids data=
   execute CJ G () ids (KJ (execute (I7 A k ell B σ) G () ids data)):= by
 funext v
 unfold execute I6
 rw [Ff.CM]
 have hInput: Ff.L0
     (C7.transform (I7 A k ell B σ) (fun _ z=>z) (fun _ _ z=>z.report))
     (fun _ _ _ z=>z) G () ids data=
     KJ (execute (I7 A k ell B σ) G () ids data):=by
   funext w
   exact C7.A4 _ _ _ G ids data w
 rw [hInput]
 rfl
include hi in
lemma oY:∃M,ReportsMatching G ids (execute (I6 A k ell B σ) G () ids data) M:= by
 rw [t0]
 exact ⟨_,jJ G ids hi _⟩
end Be
end
noncomputable section
namespace Be
lemma nR {I: Type} (A B: ℕ→ Deterministic Unit I I) (n: ℕ)
   (h:∀i<n,A i=B i): IM.MR A n=IM.MR B n:= by
 induction n with
 | zero => rfl
 | succ n ih =>
   rw [IM.MR,IM.MR,ih (fun i hi=>h i (by omega)),h n (by omega)]
lemma vD {K: Type} (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   (size ell L P: ℕ) (s t: ℕ→ IJ) (h:∀i<P,s i=t i):
   If A k size ell L P s=If A k size ell L P t:= by
 unfold If
 congr 1
 apply nR
 intro i hi
 rw [h i hi]
end Be
end
noncomputable section
namespace Be
variable {K: Type} {N ell B: ℕ} {G M0: SimpleGraph (Fin N)} {ids: Fin N→ ℕ}
   (hi: Function.Injective ids) (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   (hOracle: qH A k G ids (zX ell) B)
   (hB: 0<B) (hOpt: optimum G≤ B*matchingSize M0) (hell: 0<ell)
   (data0: Fin N→ Ln) (hNei:∀v,(data0 v).neighbors=neighborIDs G ids v)
   (hReports: ReportsMatching G ids (KJ data0) M0)
include hi hOracle hB hOpt hell hNei hReports in
lemma Jd:∃(σ: Bj ell B) (M: SimpleGraph (Fin N)),
   ReportsMatching G ids (execute (I6 A k ell B σ) G () ids data0) M∧
     ell*optimum G≤(ell+2)*matchingSize M:= by
 let run:=zI hi A k hOracle hB hOpt hell data0 hNei hReports
 let choices:=fun t=>((run t).MY hi A k hOracle hB hOpt hell).NP
 have hChoices:∀t i,i<AG ell→
     (choices t i).1<AH ell B∧(choices t i).2.1<AH ell B∧
       (choices t i).2.2<AH ell B:=by
   intro t i hi
   exact ((run t).MY _ A k hOracle hB hOpt hell).K9 i hi
 let σ: Bj ell B:=fun t i=>
   (⟨(choices t.val i.val).1,(hChoices t.val i.val i.isLt).1⟩,
     ⟨(choices t.val i.val).2.1,(hChoices t.val i.val i.isLt).2.1⟩,
     ⟨(choices t.val i.val).2.2,(hChoices t.val i.val i.isLt).2.2⟩)
 have hAgree:∀t<KT ell B,∀i<AG ell,Kj ell B σ t i=choices t i:=by
   intro t ht i hi
   unfold Kj
   rw [dif_pos ht,dif_pos hi]
 have hPrograms: I7 A k ell B σ=IM.MR
     (fun t=>If A k (zX ell) ell (Ey ell+1)
       (AG ell) (choices t)) (KT ell B):=by
   apply nR
   intro t ht
   exact vD A k _ _ _ _ _ _ (hAgree t ht)
 have hData: execute (I7 A k ell B σ) G () ids data0=(run (KT ell B)).data:=by
   rw [hPrograms]
   exact (l2 hi A k hOracle hB hOpt hell data0 hNei hReports (KT ell B)).symm
 refine ⟨σ,(run (KT ell B)).MG,?_,?_⟩
 · rw [t0,hData,fL G ids _ _ (run (KT ell B)).Nn]
   exact (run (KT ell B)).Nn
 · exact bJ hi A k hOracle hB hOpt hell data0 hNei hReports
end Be
end
noncomputable section
namespace Be
variable {N: ℕ}
def wR (H: SimpleGraph (Fin N)) (r: Fin N): Finset (Fin N):=
 univ.filter (H.Reachable r)
lemma nB (H: SimpleGraph (Fin N)) (r v: Fin N):
   v∈wR H r↔ H.Reachable r v:= by simp [wR]
lemma mO (H: SimpleGraph (Fin N)) (r u v: Fin N)
   (hu: u∈wR H r) (hEdge: H.Adj u v): v∈wR H r:=
 (nB H r v).mpr (((nB H r u).mp hu).trans hEdge.reachable)
lemma oV (H: SimpleGraph (Fin N)) (r u: Fin N)
   (hu: u∈wR H r): wR H u=wR H r:= by
 ext v
 rw [nB,nB]
 have hru:=(nB H r u).mp hu
 exact ⟨fun h=>hru.trans h,fun h=>hru.symm.trans h⟩
namespace C3
variable {H M: SimpleGraph (Fin N)} (P: C3 H M)
lemma A8 (i: ℕ) (hi: i≤ 2*P.length+1): H.Reachable (P.vertex 0) (P.vertex i):= by
 induction i with
 | zero => exact SimpleGraph.Reachable.refl _
 | succ i ih => exact (ih (by omega)).trans (P.Mu i (by omega)).reachable
lemma p7: P.support⊆wR H (P.vertex 0):= by
 intro v hv
 obtain ⟨i,hi,rfl⟩:=mem_image.mp hv
 exact (nB H _ _).mpr (P.A8 i (by have hh:=mem_range.mp hi;omega))
lemma v3 (u: Fin N) (hu: u∈P.support):
   ∃v∈P.support,H.Adj u v∧¬M.Adj u v:= by
 obtain ⟨i,hi,rfl⟩:=mem_image.mp hu
 have hi': i≤ 2*P.length+1:= by have h:=mem_range.mp hi;omega
 by_cases hOdd: Odd i
 · have hI: 0< i:= by rw [Nat.odd_iff] at hOdd;omega
   refine ⟨P.vertex (i-1),P.mem_support (i-1) (by omega),?_,?_⟩
   · have hh:=(P.Mu (i-1) (by omega)).symm
     simpa only [Nat.sub_add_cancel (by omega: 1≤ i)] using hh
   · intro hM
     have hh:=(P.MG (i-1) (by omega)).mp (by
       simpa only [Nat.sub_add_cancel (by omega: 1≤ i)] using hM.symm)
     rw [Nat.odd_iff] at hh hOdd
     omega
 · have hI: i≤ 2*P.length:= by rw [Nat.odd_iff] at hOdd;omega
   refine ⟨P.vertex (i+1),P.mem_support (i+1) (by omega),P.Mu i hI,?_⟩
   intro hM
   exact hOdd ((P.MG i hI).mp hM)
lemma qD {G K: SimpleGraph (Fin N)} (hM: Matching G M) (hK: Matching G K)
   (P: C3 (M⊔K) M):
   ∀u,u∈P.support→∀v,(M⊔K).Adj u v→ v∈P.support:= by
 intro u hu v hEdge
 rcases hEdge with hEdge|hEdge
 · exact P.B7 ⟨le_sup_left,hM.2⟩ u hu v hEdge
 · obtain ⟨w,hw,hUW,hNotM⟩:=P.v3 u hu
   have hKuw: K.Adj u w:=hUW.resolve_left hNotM
   have hVW:=qJ.gP G K hK u v w hEdge hKuw
   exact hVW.symm ▸hw
lemma qC {G K: SimpleGraph (Fin N)} (hM: Matching G M) (hK: Matching G K)
   (P: C3 (M⊔K) M):
   (wR (M⊔K) (P.vertex 0)).card≤ 2*P.length+2:= by
 have hClosed:=P.qD hM hK
 have hSub: wR (M⊔K) (P.vertex 0)⊆P.support:= by
   intro v hv
   obtain ⟨w⟩:=(nB _ _ _).mp hv
   exact C1 hClosed w (P.mem_support 0 (by omega))
 simpa only [P.IB] using card_le_card hSub
end C3
end Be
end
noncomputable section
namespace Be
variable {N: ℕ}
def Jh (H: SimpleGraph (Fin N)) (C: Finset (Fin N)): SimpleGraph (Fin N) where
 Adj u v:=H.Adj u v∧ u∈C∧ v∈C
 symm:=⟨fun _ _ h=>⟨h.1.symm,h.2.2,h.2.1⟩⟩
 loopless:=⟨fun _ h=>h.1.ne rfl⟩
lemma o1 {H J: SimpleGraph (Fin N)} (hJ: Matching H J) (C: Finset (Fin N)):
   Matching H (Jh J C):= by
 apply tB.n4
 · intro u v h;exact hJ.1 h.1
 · intro u v w huv huw
   exact qJ.gP H J hJ u v w huv.1 huw.1
namespace C3
variable {H J: SimpleGraph (Fin N)} (P: C3 H J) (C: Finset (Fin N))
   (hInside: P.support⊆C)
def Je: C3 H (Jh J C) where
 length:=P.length
 vertex:=P.vertex
 injective:=P.injective
 Mu:=P.Mu
 MG:=by
   intro i hi
   constructor
   · intro h;exact (P.MG i hi).mp h.1
   · intro h
     exact ⟨(P.MG i hi).mpr h,hInside (P.mem_support i (by omega)),hInside (P.mem_support (i+1) (by omega))⟩
 Ki:=fun w h=>P.Ki w h.1
 LP:=fun w h=>P.LP w h.1
lemma bZ (u v: Fin N)
   (h:(exchange (Jh J C) (P.Je C hInside).Nm (P.Je C hInside).added).Adj u v):
   u∈C:= by
 rcases h with h|h
 · exact h.1.2.1
 · have hEdge:=(P.Je C hInside).added.mem_edgeFinset.mpr
     ((P.Je C hInside).added.mem_edgeSet.mpr h)
   have hu:=(P.Je C hInside).Fp s(u,v) hEdge u (Sym2.mem_mk_left _ _)
   exact hInside hu
end C3
structure tD (H M J: SimpleGraph (Fin N)) (R: ℕ): Prop where
 MG: Matching H J
 GK:∀v,(wR H v).card≤ R→∀Q: SimpleGraph (Fin N),
   Matching H Q→(∀u w,Q.Adj u w→ u∈wR H v)→
   matchingSize Q≤ matchingSize (Jh J (wR H v))
 HI:∀v,R<(wR H v).card→∀u∈wR H v,
   ∀w,H.Adj u w→(J.Adj u w↔ M.Adj u w)
lemma tD.MI {G M K J: SimpleGraph (Fin N)} {r: ℕ}
   (hM: Matching G M) (hK: Matching G K)
   (hSpec: tD (M⊔K) M J (2*r+2))
   (P: C3 (M⊔K) J) (hLength: P.length≤ r): False:= by
 let C:=wR (M⊔K) (P.vertex 0)
 have hInside: P.support⊆C:=P.p7
 by_cases hSmall: C.card≤ 2*r+2
 · let Q:=Jh J C
   let P':=P.Je C hInside
   have hQ: Matching (M⊔K) Q:=o1 hSpec.MG C
   have hAug:=P'.Bo hQ
   have hAugInside:∀u w,(exchange Q P'.Nm P'.added).Adj u w→ u∈C:=
     fun u w h=>P.bZ C hInside u w h
   have hMax:=hSpec.GK (P.vertex 0) hSmall _ hAug.1 hAugInside
   rw [hAug.2] at hMax
   change matchingSize Q+1≤ matchingSize Q at hMax
   omega
 · have hLarge: 2*r+2< C.card:=by omega
   have hAgree:∀u∈C,∀w,(M⊔K).Adj u w→(J.Adj u w↔ M.Adj u w):=
     hSpec.HI (P.vertex 0) hLarge
   let Q: C3 (M⊔K) M:={
     length:=P.length
     vertex:=P.vertex
     injective:=P.injective
     Mu:=P.Mu
     MG:=by
       intro i hi
       exact (hAgree _ (hInside (P.mem_support i (by omega))) _ (P.Mu i hi)).symm.trans (P.MG i hi)
     Ki:=by
       intro w h
       exact P.Ki w ((hAgree _ (hInside (P.mem_support 0 (by omega))) w (Or.inl h)).mpr h)
     LP:=by
       intro w h
       exact P.LP w ((hAgree _ (hInside (P.mem_support (2*P.length+1) le_rfl)) w (Or.inl h)).mpr h)}
   have hCard:=Q.qC hM hK
   change C.card≤ 2*P.length+2 at hCard
   omega
lemma tD.IW {G M K J: SimpleGraph (Fin N)} {r: ℕ}
   (hM: Matching G M) (hK: Matching G K)
   (hSpec: tD (M⊔K) M J (2*r+2)):
   r*optimum (M⊔K)≤(r+2)*matchingSize J:= by
 by_contra hBad
 have hBad':(r+2)*matchingSize J< r*optimum (M⊔K):=by omega
 obtain ⟨F,hDisjoint,hShort,hMax,hLarge⟩:=aU hSpec.MG r hBad'
 have hEmpty: F=∅:=eq_empty_iff_forall_notMem.mpr (fun P hP=>hSpec.MI hM hK P (hShort P hP))
 simp [hEmpty] at hLarge
lemma tD.NF {G M K J: SimpleGraph (Fin N)} {r: ℕ}
   (hM: Matching G M) (hK: Matching G K)
   (hSpec: tD (M⊔K) M J (2*r+2)):
   r*matchingSize M≤(r+2)*matchingSize J∧ r*matchingSize K≤(r+2)*matchingSize J:= by
 have hApprox:=hSpec.IW hM hK
 have hM': Matching (M⊔K) M:=⟨le_sup_left,hM.2⟩
 have hK': Matching (M⊔K) K:=⟨le_sup_right,hK.2⟩
 exact ⟨(Nat.mul_le_mul_left r (qJ.gQ _ _ hM')).trans hApprox,
   (Nat.mul_le_mul_left r (qJ.gQ _ _ hK')).trans hApprox⟩
end Be
end
noncomputable section
namespace Be
variable {N: ℕ}
def Fg (E: Finset (Sym2 ℕ)): Prop:=
 (∀e∈E,¬e.IsDiag)∧ Set.Pairwise (E: Set (Sym2 ℕ)) (fun e f=>Disjoint e.toFinset f.toFinset)
lemma r2: Fg ∅:= by
 constructor
 · intro e he;simp at he
 · intro e he;simp at he
lemma Fg.Ch {E: Finset (Sym2 ℕ)} (hE: Fg E)
   (u v w: ℕ) (hUV: s(u,v)∈E) (hUW: s(u,w)∈E): v=w:= by
 apply (Sym2.mkEmbedding u).injective
 by_contra hNe
 exact disjoint_left.mp (hE.2 hUV hUW hNe)
   (Sym2.mem_toFinset.mpr (Sym2.mem_mk_left _ _)) (Sym2.mem_toFinset.mpr (Sym2.mem_mk_left _ _))
lemma pD (E: Finset (Sym2 ℕ)):
   ∃F: Finset (Sym2 ℕ),F⊆E∧ Fg F∧
     ∀K: Finset (Sym2 ℕ),K⊆E→ Fg K→ K.card≤ F.card:= by
 let S:=E.powerset.filter Fg
 have hEmpty:(∅: Finset (Sym2 ℕ))∈S:=by simp [S,r2]
 obtain ⟨F,hF,hCard⟩:=exists_mem_eq_sup S ⟨∅,hEmpty⟩ Finset.card
 have hFS:=(mem_filter.mp hF).1
 have hFM:=(mem_filter.mp hF).2
 refine ⟨F,mem_powerset.mp hFS,hFM,?_⟩
 intro K hKE hKM
 have hKS: K∈S:=mem_filter.mpr ⟨mem_powerset.mpr hKE,hKM⟩
 exact (le_sup (f:=Finset.card) hKS).trans_eq hCard
def HT (E: Finset (Sym2 ℕ)): Finset (Sym2 ℕ):=(pD E).choose
lemma xL (E: Finset (Sym2 ℕ)):
   HT E⊆E∧ Fg (HT E)∧
     ∀K: Finset (Sym2 ℕ),K⊆E→ Fg K→ K.card≤(HT E).card:=
 (pD E).choose_spec
def H5 (E: Finset (Sym2 ℕ)) (u: ℕ): Option ℕ:=
 if h:∃v,s(u,v)∈E then some h.choose else none
lemma xY (E: Finset (Sym2 ℕ)) (hE: Fg E) (u v: ℕ):
   H5 E u=some v↔ s(u,v)∈E:= by
 unfold H5
 split_ifs with h
 · constructor
   · intro hV
     have hEq:=Option.some.inj hV
     rw [←hEq]
     exact h.choose_spec
   · intro hV
     congr 1
     exact hE.Ch u h.choose v h.choose_spec hV
 · constructor
   · intro hh;cases hh
   · intro hV;exact (h ⟨v,hV⟩).elim
def KG (H: SimpleGraph (Fin N)) (ids: Fin N→ ℕ): Finset (Sym2 ℕ):=
 H.edgeFinset.image (Sym2.map ids)
lemma Ce (H: SimpleGraph (Fin N)) (ids: Fin N→ ℕ) (hi: Function.Injective ids):
   (KG H ids).card=matchingSize H:= card_image_of_injective _ (Sym2.map.injective hi)
lemma Ej (H: SimpleGraph (Fin N)) (ids: Fin N→ ℕ) (hi: Function.Injective ids) (u v: Fin N):
   s(ids u,ids v)∈KG H ids↔ H.Adj u v:= by
 constructor
 · intro h
   obtain ⟨e,he,hEq⟩:=mem_image.mp h
   have hE: e=s(u,v):=(Sym2.map.injective hi) hEq
   rw [hE] at he
   exact H.mem_edgeSet.mp (H.mem_edgeFinset.mp he)
 · intro h
   exact mem_image.mpr ⟨s(u,v),H.mem_edgeFinset.mpr (H.mem_edgeSet.mpr h),rfl⟩
lemma r0 {G M: SimpleGraph (Fin N)} (hM: Matching G M)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids): Fg (KG M ids):= by
 constructor
 · intro e he
   obtain ⟨f,hf,rfl⟩:=mem_image.mp he
   exact fun h=>M.not_isDiag_of_mem_edgeFinset hf ((Sym2.isDiag_map hi).mp h)
 · intro e he f hf hNe
   obtain ⟨a,ha,rfl⟩:=mem_image.mp he
   obtain ⟨b,hb,rfl⟩:=mem_image.mp hf
   apply disjoint_left.mpr
   intro j hJA hJB
   obtain ⟨u,hu,hUJ⟩:=Sym2.mem_map.mp (Sym2.mem_toFinset.mp hJA)
   obtain ⟨v,hv,hVJ⟩:=Sym2.mem_map.mp (Sym2.mem_toFinset.mp hJB)
   have hUV: u=v:=hi (hUJ.trans hVJ.symm)
   have hAB: a≠b:=fun h=>hNe (congrArg (Sym2.map ids) h)
   exact hM.2 ⟨a,M.mem_edgeFinset.mp ha⟩ (mem_univ _) ⟨b,M.mem_edgeFinset.mp hb⟩ (mem_univ _)
     (fun h=>hAB (congrArg Subtype.val h)) u hu (hUV.symm ▸hv)
end Be
end
noncomputable section
namespace Be
variable {N: ℕ}
def KH (E: Finset (Sym2 ℕ)) (hLoop:∀e∈E,¬e.IsDiag)
   (ids: Fin N→ ℕ): SimpleGraph (Fin N) where
 Adj u v:=s(ids u,ids v)∈E
 symm:=⟨by intro u v h;simpa only [Sym2.eq_swap] using h⟩
 loopless:=⟨fun u h=>hLoop _ h (by simp)⟩
lemma r1 (H: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (hi: Function.Injective ids) (E: Finset (Sym2 ℕ)) (hE: Fg E)
   (hSub: E⊆KG H ids): Matching H (KH E hE.1 ids):= by
 apply tB.n4
 · intro u v h
   exact (Ej H ids hi u v).mp (hSub h)
 · intro u v w huv huw
   exact hi (hE.Ch (ids u) (ids v) (ids w) huv huw)
lemma Av (H: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (hi: Function.Injective ids) (E: Finset (Sym2 ℕ)) (hE: Fg E)
   (hSub: E⊆KG H ids): KG (KH E hE.1 ids) ids=E:= by
 ext e
 constructor
 · intro he
   obtain ⟨f,hf,rfl⟩:=mem_image.mp he
   obtain ⟨⟨u,v⟩,hF⟩:=f.exists_rep
   rw [←hF] at hf ⊢
   exact (KH E hE.1 ids).mem_edgeSet.mp ((KH E hE.1 ids).mem_edgeFinset.mp hf)
 · intro he
   obtain ⟨f,hf,hEq⟩:=mem_image.mp (hSub he)
   obtain ⟨⟨u,v⟩,hF⟩:=f.exists_rep
   have hMap: Sym2.map ids s(u,v)=e:=(congrArg (Sym2.map ids) hF).trans hEq
   have hUV:(KH E hE.1 ids).Adj u v:= by
     change Sym2.map ids s(u,v)∈E
     rw [hMap]
     exact he
   exact mem_image.mpr ⟨s(u,v),(KH E hE.1 ids).mem_edgeFinset.mpr
     ((KH E hE.1 ids).mem_edgeSet.mpr hUV),hMap⟩
lemma Cf (H: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (hi: Function.Injective ids) (E: Finset (Sym2 ℕ)) (hE: Fg E)
   (hSub: E⊆KG H ids): matchingSize (KH E hE.1 ids)=E.card:= by
 rw [←Ce _ ids hi,Av H ids hi E hE hSub]
lemma xX (H: SimpleGraph (Fin N)) (C: Finset (Fin N))
   (Q: SimpleGraph (Fin N)) (hQ: Q≤ H) (hInside:∀u v,Q.Adj u v→ u∈C)
   (ids: Fin N→ ℕ): KG Q ids⊆KG (Jh H C) ids:= by
 apply image_subset_image
 apply SimpleGraph.edgeFinset_mono
 intro u v h
 exact ⟨hQ h,hInside u v h,hInside v u h.symm⟩
def zY (H: SimpleGraph (Fin N)) (C: Finset (Fin N)) (ids: Fin N→ ℕ): SimpleGraph (Fin N):=
 KH (HT (KG (Jh H C) ids))
   (xL _).2.1.1 ids
lemma eY (H: SimpleGraph (Fin N)) (C: Finset (Fin N))
   (ids: Fin N→ ℕ) (hi: Function.Injective ids): Matching H (zY H C ids):= by
 have h:=r1 (Jh H C) ids hi _ (xL _).2.1 (xL _).1
 exact ⟨fun _ _ hEdge=>(h.1 hEdge).1,h.2⟩
lemma iO (H: SimpleGraph (Fin N)) (C: Finset (Fin N))
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (u v: Fin N)
   (h:(zY H C ids).Adj u v): H.Adj u v∧ u∈C∧ v∈C:= by
 apply (Ej (Jh H C) ids hi u v).mp
 exact (xL _).1 h
lemma f9 (H: SimpleGraph (Fin N)) (C: Finset (Fin N))
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (Q: SimpleGraph (Fin N))
   (hQ: Matching H Q) (hInside:∀u v,Q.Adj u v→ u∈C):
   matchingSize Q≤ matchingSize (zY H C ids):= by
 have hSub:=xX H C Q hQ.1 hInside ids
 have hMax:=(xL (KG (Jh H C) ids)).2.2
   (KG Q ids) hSub (r0 hQ ids hi)
 rw [Ce Q ids hi] at hMax
 have hCard:=Cf (Jh H C) ids hi _ (xL _).2.1 (xL _).1
 exact hMax.trans_eq hCard.symm
end Be
end
noncomputable section
namespace Be
variable {N: ℕ}
lemma Cg (H: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (hi: Function.Injective ids) (E: Finset (Sym2 ℕ)) (hSub: E⊆KG H ids)
   (u: Fin N) (j: ℕ) (hE: s(ids u,j)∈E):
   ∃v,H.Adj u v∧ s(ids u,ids v)∈E∧ ids v=j:= by
 obtain ⟨f,hf,hMap⟩:=mem_image.mp (hSub hE)
 have hOwn: ids u∈Sym2.map ids f:= by rw [hMap];exact Sym2.mem_mk_left _ _
 obtain ⟨a,ha,hAU⟩:=Sym2.mem_map.mp hOwn
 have hA: a=u:=hi hAU
 subst a
 obtain ⟨v,hF⟩:=Sym2.mem_iff_exists.mp ha
 rw [hF] at hf hMap
 have hV: ids v=j:=(Sym2.mkEmbedding (ids u)).injective hMap
 refine ⟨v,H.mem_edgeSet.mp (H.mem_edgeFinset.mp hf),?_,hV⟩
 simpa only [hV] using hE
lemma uY (H: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (hi: Function.Injective ids) (E: Finset (Sym2 ℕ)) (hE: Fg E)
   (hSub: E⊆KG H ids):
   ReportsMatching H ids (fun v=>H5 E (ids v)) (KH E hE.1 ids):= by
 refine ⟨r1 H ids hi E hE hSub,?_⟩
 intro v
 have hSome (j: ℕ): H5 E (ids v)=some j↔
     ∃w,(KH E hE.1 ids).Adj v w∧ ids w=j:= by
   constructor
   · intro h
     have hNatural:=(xY E hE (ids v) j).mp h
     obtain ⟨w,hVW,hEdge,hId⟩:=Cg H ids hi E hSub v j hNatural
     exact ⟨w,hEdge,hId⟩
   · rintro ⟨w,hEdge,hId⟩
     apply (xY E hE (ids v) j).mpr
     change s(ids v,ids w)∈E at hEdge
     simpa only [hId] using hEdge
 refine ⟨?_,hSome⟩
 constructor
 · intro hNone w hEdge
   change H5 E (ids v)=none at hNone
   have hSome':=(hSome (ids w)).mpr ⟨w,hEdge,rfl⟩
   rw [hNone] at hSome'
   cases hSome'
 · intro hFree
   cases hOut: H5 E (ids v) with
   | none => exact hOut
   | some j =>
     obtain ⟨w,hEdge,hId⟩:=(hSome j).mp hOut
     exact (hFree w hEdge).elim
end Be
end
noncomputable section
namespace Be
variable {N: ℕ} {I: Type}
def BD (H: SimpleGraph (Fin N)) (ids: Fin N→ ℕ) (inp: Fin N→ I) (v: Fin N):
   Finset (ℕ ×I):=(wR H v).image (fun u=>(ids u,inp u))
lemma eZ (H: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (hi: Function.Injective ids) (inp: Fin N→ I) (v: Fin N):
   ((BD H ids inp v).image Prod.fst).card=(wR H v).card:= by
 unfold BD
 rw [image_image]
 exact card_image_of_injective _ hi
lemma iS (H: SimpleGraph (Fin N)) (r v: Fin N)
   (hv: v∈wR H r): Close H (wR H r).card r v:= by
 obtain ⟨w,hPath,hLength⟩:=((nB H r v).mp hv).exists_path_of_dist
 have hSub: w.support.toFinset⊆wR H r:= by
   intro u hu
   exact (nB H r u).mpr ⟨w.takeUntil u (List.mem_toFinset.mp hu)⟩
 have hCard:=card_le_card hSub
 rw [List.toFinset_card_of_nodup hPath.support_nodup,SimpleGraph.Walk.length_support] at hCard
 exact ⟨w,by omega⟩
lemma gE (H: SimpleGraph (Fin N)) (ids: Fin N→ ℕ) (inp: Fin N→ I)
   (r: ℕ) (v: Fin N) (hSmall:(wR H v).card≤ r):
   JW.NK H ids inp r v=(wR H v).image (fun u=>(ids u,inp u)):= by
 ext z
 constructor
 · intro hz
   obtain ⟨u,hReach,hEq⟩:=BM H ids inp r v z hz
   exact mem_image.mpr ⟨u,(nB H v u).mpr hReach,hEq.symm⟩
 · intro hz
   obtain ⟨u,hu,rfl⟩:=mem_image.mp hz
   obtain ⟨w,hW⟩:=iS H v u hu
   exact JW.Km H ids inp r w (hW.trans hSmall)
def G7 (neighbors: I→ Finset ℕ) (R: Finset (ℕ ×I)): Prop:=
 ∀z∈R,neighbors z.2⊆R.image Prod.fst
lemma mR (H: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (hi: Function.Injective ids) (inp: Fin N→ I) (neighbors: I→ Finset ℕ)
   (hNeighbors:∀u,neighbors (inp u)=neighborIDs H ids u) (r: ℕ) (v: Fin N)
   (hClosed: G7 neighbors (JW.NK H ids inp r v)):
   JW.NK H ids inp r v=(wR H v).image (fun u=>(ids u,inp u)):= by
 let R:=JW.NK H ids inp r v
 let C:=univ.filter (fun u=>(ids u,inp u)∈R)
 have hAdjClosed:∀u∈C,∀w,H.Adj u w→ w∈C:= by
   intro u hu w hUW
   have hU:(ids u,inp u)∈R:=(mem_filter.mp hu).2
   have hWId: ids w∈R.image Prod.fst:= by
     apply hClosed (ids u,inp u) hU
     rw [hNeighbors u]
     exact mem_image.mpr ⟨w,(H.mem_neighborFinset u w).mpr hUW,rfl⟩
   obtain ⟨z,hz,hId⟩:=mem_image.mp hWId
   obtain ⟨a,hA⟩:=JW.BL H ids inp r v z hz
   rw [hA] at hz hId
   have hAW: a=w:=hi hId
   rw [hAW] at hz
   exact mem_filter.mpr ⟨mem_univ _,hz⟩
 have hSub: wR H v⊆C:= by
   intro u hu
   obtain ⟨w⟩:=(nB H v u).mp hu
   exact C1 hAdjClosed w (mem_filter.mpr ⟨mem_univ _,JW.Kl H ids inp r v⟩)
 ext z
 constructor
 · intro hz
   obtain ⟨u,hReach,hEq⟩:=BM H ids inp r v z hz
   exact mem_image.mpr ⟨u,(nB H v u).mpr hReach,hEq.symm⟩
 · intro hz
   obtain ⟨u,hu,rfl⟩:=mem_image.mp hz
   exact (mem_filter.mp (hSub hu)).2
lemma c0 (H: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (hi: Function.Injective ids) (inp: Fin N→ I) (neighbors: I→ Finset ℕ)
   (hNeighbors:∀u,neighbors (inp u)=neighborIDs H ids u) (r: ℕ) (v: Fin N)
   (hClosed: G7 neighbors (JW.NK H ids inp r v)):
   ((JW.NK H ids inp r v).image Prod.fst).card=(wR H v).card:= by
 rw [mR H ids hi inp neighbors hNeighbors r v hClosed,image_image]
 exact card_image_of_injective _ hi
end Be
end
noncomputable section
namespace Be
variable {K I O: Type}
def KL (A: Deterministic K I O) (k: K) (fallback: O):
   Deterministic Unit (Finset ℕ ×I) O:=
 C7.transform (C7.NE (Fb.Me A) (k,1))
   (fun id inp=>{(id,inp.2,inp.1)})
   (fun id _ out=>(out id).getD fallback)
lemma u4 (A: Deterministic K I O) (k: K) (fallback: O)
   {N: ℕ} (G H: SimpleGraph (Fin N)) (hHG: H≤ G)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (inp: Fin N→ I):
   execute (KL A k fallback) G () ids (fun v=>(neighborIDs H ids v,inp v))=
     execute A H k ids inp:= by
 let D: Routed G (Fin N):={
   graph:=H
   owner:=id
   identity:=ids
   identity_injective:=hi
   route:=fun u v h=>(hHG h).toWalk}
 have hD: RouteLength D 1:=by intro u v h;exact le_rfl
 have hInput:(fun v=>({(ids v,inp v,neighborIDs H ids v)}: Finset (Fb.Nx I)))=
     Fb.HL D inp:= by
   funext v
   simp only [Fb.HL,D,id_eq,filter_eq',mem_univ,if_true,image_singleton,Fb.NJ]
   have hN: H.neighborFinset v=univ.filter (H.Adj v):=by ext w;simp
   simp only [neighborIDs,hN]
 funext v
 unfold execute KL
 rw [C7.A4,C7.FS,hInput]
 have hOut:=Fb.yQ D ids inp A k 1 hD v
 have hEval:=congrArg (fun z: Option O=>z.getD fallback) hOut
 exact hEval
def gather (I: Type): Deterministic ℕ I (Finset (ℕ ×I)) where
 program:={
   State:=Finset (ℕ ×I)
   Msg:=Finset (ℕ ×I)
   rounds:=id
   init:=fun _ id inp _=>{(id,inp)}
   send:=id
   step:=JW.merge
   out:=id}
 tape_independent:=by intros;rfl
lemma Kr {N: ℕ} (H: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (inp: Fin N→ I) (r t: ℕ):∀v,
   (gather I).program.run H r ids inp (fun _ _=>false) t v=JW.NK H ids inp t v:= by
 induction t with
 | zero => intro v;rfl
 | succ t ih =>
   intro v
   rw [SmoothedMIS.LocalAlg.run]
   simp only [ih]
   have hN: univ.filter (H.Adj v)=H.neighborFinset v:=by ext w;simp
   change JW.merge _ (((univ.filter (H.Adj v)).val.map _))=_
   rw [hN]
   rfl
lemma DS {N: ℕ} (H: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (inp: Fin N→ I) (r: ℕ) (v: Fin N):
   execute (gather I) H r ids inp v=JW.NK H ids inp r v:= by
 unfold execute SmoothedMIS.LocalAlg.output
 exact Kr H ids inp r r v
def EU (I: Type) (r: ℕ): Deterministic Unit (Finset ℕ ×I) (Finset (ℕ ×I)):=
 KL (gather I) r ∅
lemma lV {N: ℕ} (G H: SimpleGraph (Fin N)) (hHG: H≤ G)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (inp: Fin N→ I) (r: ℕ) (v: Fin N):
   execute (EU I r) G () ids (fun v=>(neighborIDs H ids v,inp v)) v=
     JW.NK H ids inp r v:= by
 unfold EU
 rw [u4 _ _ _ G H hHG ids hi inp]
 exact DS H ids inp r v
end Be
end
noncomputable section
namespace Be
variable {N: ℕ}
def Du (H M: SimpleGraph (Fin N)) (ids: Fin N→ ℕ) (R: ℕ): SimpleGraph (Fin N) where
 Adj u v:=H.Adj u v∧ if (wR H u).card≤ R then
   (zY H (wR H u) ids).Adj u v else M.Adj u v
 symm:=⟨by
   intro u v h
   have hC:=oV H u v ((nB H u v).mpr h.1.reachable)
   refine ⟨h.1.symm,?_⟩
   rw [hC]
   split_ifs at h ⊢with hSmall
   · exact h.2.symm
   · exact h.2.symm⟩
 loopless:=⟨fun _ h=>h.1.ne rfl⟩
lemma iP {G H M: SimpleGraph (Fin N)} (hM: Matching G M)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (R: ℕ):
   Matching H (Du H M ids R):= by
 apply tB.n4
 · intro u v h;exact h.1
 · intro u v w huv huw
   have hV:=huv.2
   have hW:=huw.2
   by_cases hSmall:(wR H u).card≤ R
   · rw [if_pos hSmall] at hV hW
     exact qJ.gP H _
       (eY H (wR H u) ids hi) u v w hV hW
   · rw [if_neg hSmall] at hV hW
     exact qJ.gP G M hM u v w hV hW
lemma oU (H M: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (hi: Function.Injective ids) (R: ℕ) (v: Fin N) (hSmall:(wR H v).card≤ R):
   Jh (Du H M ids R) (wR H v)=
     zY H (wR H v) ids:= by
 ext u w
 constructor
 · intro h
   have hC:=oV H v u h.2.1
   have hh:=h.1.2
   rw [hC,if_pos hSmall] at hh
   exact hh
 · intro h
   have hInside:=iO H (wR H v) ids hi u w h
   have hC:=oV H v u hInside.2.1
   refine ⟨⟨hInside.1,?_⟩,hInside.2.1,hInside.2.2⟩
   rw [hC,if_pos hSmall]
   exact h
lemma q4 {G H M: SimpleGraph (Fin N)} (hM: Matching G M)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (R: ℕ):
   tD H M (Du H M ids R) R where
 MG:=iP hM ids hi R
 GK:=by
   intro v hSmall Q hQ hInside
   rw [oU H M ids hi R v hSmall]
   exact f9 H (wR H v) ids hi Q hQ hInside
 HI:=by
   intro v hLarge u hu w hEdge
   have hC:=oV H v u hu
   change (H.Adj u w∧(if (wR H u).card≤ R then _ else M.Adj u w))↔ M.Adj u w
   rw [hC,if_neg (by omega:¬(wR H v).card≤ R)]
   simp only [hEdge,true_and]
lemma mN {G M K: SimpleGraph (Fin N)} (hM: Matching G M) (hK: Matching G K)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (r: ℕ):
   r*matchingSize M≤(r+2)*matchingSize (Du (M⊔K) M ids (2*r+2))∧
   r*matchingSize K≤(r+2)*matchingSize (Du (M⊔K) M ids (2*r+2)):=
 (q4 hM ids hi (2*r+2)).NF hM hK
end Be
end
noncomputable section
namespace Be
variable {N: ℕ}
abbrev JY:= Finset ℕ ×Option ℕ
local instance Ca: DecidableEq JY:= Classical.decEq _
def Ao (R: Finset (ℕ ×JY)): Finset (Sym2 ℕ):=
 R.biUnion (fun z=>z.2.1.image (fun j=>s(z.1,j)))
lemma eA (H: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (out: Fin N→ Option ℕ) (v: Fin N):
   Ao (BD H ids (fun u=>(neighborIDs H ids u,out u)) v)=
     KG (Jh H (wR H v)) ids:= by
 ext e
 constructor
 · intro he
   obtain ⟨z,hz,he⟩:=mem_biUnion.mp he
   obtain ⟨u,hu,rfl⟩:=mem_image.mp hz
   obtain ⟨j,hj,rfl⟩:=mem_image.mp he
   obtain ⟨w,hw,rfl⟩:=mem_image.mp hj
   have hUW:=(H.mem_neighborFinset u w).mp hw
   have hW:=mO H v u w hu hUW
   exact mem_image.mpr ⟨s(u,w),(Jh H (wR H v)).mem_edgeFinset.mpr
     ((Jh H (wR H v)).mem_edgeSet.mpr ⟨hUW,hu,hW⟩),rfl⟩
 · intro he
   obtain ⟨f,hf,rfl⟩:=mem_image.mp he
   obtain ⟨⟨u,w⟩,hF⟩:=f.exists_rep
   rw [←hF] at hf ⊢
   have hUW:=(Jh H (wR H v)).mem_edgeSet.mp
     ((Jh H (wR H v)).mem_edgeFinset.mp hf)
   exact mem_biUnion.mpr ⟨(ids u,(neighborIDs H ids u,out u)),
     mem_image.mpr ⟨u,hUW.2.1,rfl⟩,mem_image.mpr ⟨ids w,
       mem_image.mpr ⟨w,(H.mem_neighborFinset u w).mpr hUW.1,rfl⟩,rfl⟩⟩
lemma c6 (H: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (out: Fin N→ Option ℕ) (v: Fin N):
   G7 (fun x: JY=>x.1)
     (BD H ids (fun u=>(neighborIDs H ids u,out u)) v):= by
 intro z hz j hj
 obtain ⟨u,hu,rfl⟩:=mem_image.mp hz
 obtain ⟨w,hw,rfl⟩:=mem_image.mp hj
 have hUW:=(H.mem_neighborFinset u w).mp hw
 exact mem_image.mpr ⟨(ids w,(neighborIDs H ids w,out w)),
   mem_image.mpr ⟨w,mO H v u w hu hUW,rfl⟩,rfl⟩
def Jo (Rbound: ℕ) (id: ℕ) (inp: JY) (R: Finset (ℕ ×JY)): Option ℕ:=
 if G7 (fun x: JY=>x.1) R∧(R.image Prod.fst).card≤ Rbound then
   H5 (HT (Ao R)) id else inp.2
def HX (Rbound: ℕ): Deterministic Unit JY (Option ℕ):=
 C7.transform (EU JY Rbound)
   (fun _ inp=>(inp.1,inp)) (Jo Rbound)
end Be
end
noncomputable section
namespace Be
variable {N: ℕ}
local instance kZ: DecidableEq JY:= Classical.decEq _
lemma xQ (H: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (hi: Function.Injective ids) (out: Fin N→ Option ℕ) (Rbound: ℕ) (v: Fin N):
   Jo Rbound (ids v) (neighborIDs H ids v,out v)
     (JW.NK H ids (fun u=>(neighborIDs H ids u,out u)) Rbound v)=
     if (wR H v).card≤ Rbound then
       H5 (HT (KG (Jh H (wR H v)) ids)) (ids v)
     else out v:= by
 let inp: Fin N→ JY:=fun u=>(neighborIDs H ids u,out u)
 let R:=JW.NK H ids inp Rbound v
 by_cases hSmall:(wR H v).card≤ Rbound
 · have hPacket: R=BD H ids inp v:=gE H ids inp Rbound v hSmall
   have hClosed: G7 (fun x: JY=>x.1) R:= by
     rw [hPacket]
     exact c6 H ids out v
   have hCard:(R.image Prod.fst).card≤ Rbound:= by
     have hKeys:(R.image Prod.fst).card=(wR H v).card:= by
       rw [hPacket]
       exact eZ H ids hi inp v
     exact hKeys.le.trans hSmall
   change Jo Rbound (ids v) (inp v) R= _
   rw [Jo,if_pos ⟨hClosed,hCard⟩,if_pos hSmall]
   congr 2
   change Ao R=KG (Jh H (wR H v)) ids
   rw [hPacket]
   exact eA H ids out v
 · have hNot:¬(G7 (fun x: JY=>x.1) R∧(R.image Prod.fst).card≤ Rbound):= by
     rintro ⟨hClosed,hCard⟩
     have hEq:=c0 H ids hi inp (fun x: JY=>x.1) (fun _=>rfl) Rbound v hClosed
     change (R.image Prod.fst).card=(wR H v).card at hEq
     exact hSmall (by omega)
   change Jo Rbound (ids v) (inp v) R= _
   rw [Jo,if_neg hNot,if_neg hSmall]
lemma rY (G H: SimpleGraph (Fin N)) (hHG: H≤ G)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (out: Fin N→ Option ℕ)
   (Rbound: ℕ) (v: Fin N):
   execute (HX Rbound) G () ids (fun u=>(neighborIDs H ids u,out u)) v=
     if (wR H v).card≤ Rbound then
       H5 (HT (KG (Jh H (wR H v)) ids)) (ids v)
     else out v:= by
 unfold execute HX
 rw [C7.A4]
 change Jo Rbound (ids v) _
   (execute (EU JY Rbound) G () ids
     (fun u=>(neighborIDs H ids u,(neighborIDs H ids u,out u))) v)= _
 rw [lV G H hHG ids hi (fun u=>(neighborIDs H ids u,out u)) Rbound v]
 exact xQ H ids hi out Rbound v
lemma pE (G H M: SimpleGraph (Fin N)) (hHG: H≤ G) (hMH: M≤ H)
   (ids: Fin N→ ℕ) (hi: Function.Injective ids) (out: Fin N→ Option ℕ)
   (hOut: ReportsMatching G ids out M) (Rbound: ℕ):
   ReportsMatching G ids
     (execute (HX Rbound) G () ids (fun u=>(neighborIDs H ids u,out u)))
     (Du H M ids Rbound):= by
 have hMatching:=iP (H:=H) hOut.1 ids hi Rbound
 refine ⟨⟨fun _ _ h=>hHG (hMatching.1 h),hMatching.2⟩,?_⟩
 intro v
 rw [rY G H hHG ids hi out Rbound v]
 by_cases hSmall:(wR H v).card≤ Rbound
 · rw [if_pos hSmall]
   have hLocal:=uY (Jh H (wR H v)) ids hi _
     (xL _).2.1 (xL _).1
   have hAdj (w: Fin N):(Du H M ids Rbound).Adj v w↔
       (zY H (wR H v) ids).Adj v w:= by
     change (H.Adj v w∧(if (wR H v).card≤ Rbound then _ else M.Adj v w))↔ _
     rw [if_pos hSmall]
     constructor
     · exact And.right
     · intro h
       exact ⟨(iO H (wR H v) ids hi v w h).1,h⟩
   simpa only [hAdj,zY] using hLocal.2 v
 · rw [if_neg hSmall]
   have hAdj (w: Fin N):(Du H M ids Rbound).Adj v w↔ M.Adj v w:= by
     change (H.Adj v w∧(if (wR H v).card≤ Rbound then _ else M.Adj v w))↔ _
     rw [if_neg hSmall]
     exact ⟨And.right,fun h=>⟨hMH h,h⟩⟩
   simpa only [hAdj] using hOut.2 v
end Be
end
noncomputable section
namespace Be
variable {N: ℕ}
lemma CC (G M: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (out: Fin N→ Option ℕ) (hOut: ReportsMatching G ids out M) (v: Fin N):
   (out v).toFinset=neighborIDs M ids v:= by
 ext j
 have hMem: j∈(out v).toFinset↔ out v=some j:= by cases out v<;> simp [eq_comm]
 rw [hMem]
 constructor
 · intro h
   obtain ⟨w,hVW,hId⟩:=((hOut.2 v).2 j).mp h
   exact mem_image.mpr ⟨w,(M.mem_neighborFinset v w).mpr hVW,hId⟩
 · intro h
   obtain ⟨w,hVW,hId⟩:=mem_image.mp h
   exact ((hOut.2 v).2 j).mpr ⟨w,(M.mem_neighborFinset v w).mp hVW,hId⟩
lemma xZ (M K: SimpleGraph (Fin N)) (ids: Fin N→ ℕ) (v: Fin N):
   neighborIDs M ids v∪neighborIDs K ids v=neighborIDs (M⊔K) ids v:= by
 ext j
 simp only [mem_union,neighborIDs,mem_image,SimpleGraph.mem_neighborFinset,SimpleGraph.sup_adj]
 aesop
def Ek (Rbound: ℕ): Deterministic Unit (Option ℕ ×Option ℕ) (Option ℕ):=
 C7.transform (HX Rbound)
   (fun _ inp=>(inp.1.toFinset∪inp.2.toFinset,inp.1)) (fun _ _ out=>out)
lemma k1 (G M K: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (hi: Function.Injective ids) (outM outK: Fin N→ Option ℕ)
   (hM: ReportsMatching G ids outM M) (hK: ReportsMatching G ids outK K) (Rbound: ℕ):
   ReportsMatching G ids (execute (Ek Rbound) G () ids (fun v=>(outM v,outK v)))
     (Du (M⊔K) M ids Rbound):= by
 have hInput:(fun v=>((outM v).toFinset∪(outK v).toFinset,outM v))=
     (fun v=>(neighborIDs (M⊔K) ids v,outM v)):= by
   funext v
   rw [CC G M ids outM hM v,CC G K ids outK hK v,xZ]
 have hOutput: execute (Ek Rbound) G () ids (fun v=>(outM v,outK v))=
     execute (HX Rbound) G () ids (fun v=>(neighborIDs (M⊔K) ids v,outM v)):= by
   funext v
   unfold execute Ek
   rw [C7.A4]
   change execute (HX Rbound) G () ids
     (fun v=>((outM v).toFinset∪(outK v).toFinset,outM v)) v=_
   rw [hInput]
   rfl
 rw [hOutput]
 exact pE G (M⊔K) M (sup_le hM.1.1 hK.1.1) le_sup_left ids hi outM hM Rbound
lemma k0 (G M K: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (hi: Function.Injective ids) (outM outK: Fin N→ Option ℕ)
   (hM: ReportsMatching G ids outM M) (hK: ReportsMatching G ids outK K) (r: ℕ):
   ∃J: SimpleGraph (Fin N),
     ReportsMatching G ids (execute (Ek (2*r+2)) G () ids (fun v=>(outM v,outK v))) J∧
     r*matchingSize M≤(r+2)*matchingSize J∧ r*matchingSize K≤(r+2)*matchingSize J:= by
 refine ⟨Du (M⊔K) M ids (2*r+2),k1 G M K ids hi outM outK hM hK _,?_⟩
 exact mN hM.1 hK.1 ids hi r
end Be
end
noncomputable section
namespace Fe
variable {J I O: Type} [Fintype J] (A: J→ Deterministic Unit I O)
def parallel: Deterministic Unit (J→ I) (J→ O) where
 program:={
   State:=ℕ ×((j: J)→(A j).program.State)
   Msg:=((j: J)→(A j).program.Msg)
   rounds:=fun _=>(univ: Finset J).sup (fun j=>(A j).program.rounds ())
   init:=fun _ id inp _=>(0,fun j=>(A j).program.init () id (inp j) (fun _=>false))
   send:=fun st j=>(A j).program.send (st.2 j)
   step:=fun st msgs=>(st.1+1,fun j=>if st.1<(A j).program.rounds () then
     (A j).program.step (st.2 j) (msgs.map (fun m=>m j)) else st.2 j)
   out:=fun st j=>(A j).program.out (st.2 j)}
 tape_independent:=by intros;rfl
lemma Ma (T: ℕ) (hT:∀j,(A j).program.rounds ()≤ T):
   (parallel A).program.rounds ()≤ T:= Finset.sup_le (fun j _=>hT j)
lemma LA {V: Type} [Fintype V] (G: SimpleGraph V) (ids: V→ ℕ)
   (inp: V→ J→ I) (t: ℕ):∀v,
   ((parallel A).program.run G () ids inp (fun _ _=>false) t v).1=t:= by
 induction t with
 | zero => intro v;rfl
 | succ t ih => intro v;change ((parallel A).program.run G () ids inp (fun _ _=>false) t v).1+1=t+1;rw [ih]
lemma Lb {V: Type} [Fintype V] (G: SimpleGraph V) (ids: V→ ℕ)
   (inp: V→ J→ I) (t: ℕ):∀v j,
   ((parallel A).program.run G () ids inp (fun _ _=>false) t v).2 j=
     (A j).program.run G () ids (fun v=>inp v j) (fun _ _=>false) (min t ((A j).program.rounds ())) v:= by
 induction t with
 | zero => intro v j;rfl
 | succ t ih =>
   intro v j
   change (if ((parallel A).program.run G () ids inp (fun _ _=>false) t v).1<(A j).program.rounds () then
     (A j).program.step (((parallel A).program.run G () ids inp (fun _ _=>false) t v).2 j)
       ((((univ.filter (G.Adj v)).val.map (fun w=>(parallel A).program.send
         ((parallel A).program.run G () ids inp (fun _ _=>false) t w))).map (fun m=>m j)))
     else ((parallel A).program.run G () ids inp (fun _ _=>false) t v).2 j)=_
   rw [LA]
   by_cases ht: t<(A j).program.rounds ()
   · rw [if_pos ht,show min (t+1) ((A j).program.rounds ())=t+1 by omega,SmoothedMIS.LocalAlg.run]
     rw [ih v j,show min t ((A j).program.rounds ())=t by omega]
     congr 1
     rw [Multiset.map_map]
     apply Multiset.map_congr rfl
     intro w hw
     change (A j).program.send (((parallel A).program.run G () ids inp (fun _ _=>false) t w).2 j)=_
     rw [ih w j,show min t ((A j).program.rounds ())=t by omega]
   · rw [if_neg ht,ih v j]
     congr 1
     omega
lemma Gn {V: Type} [Fintype V] (G: SimpleGraph V) (ids: V→ ℕ)
   (inp: V→ J→ I) (v: V) (j: J):
   (parallel A).program.output G () ids inp (fun _ _=>false) v j=
     (A j).program.output G () ids (fun v=>inp v j) (fun _ _=>false) v:= by
 have hT:(A j).program.rounds ()≤(parallel A).program.rounds ():=le_sup (f:=fun j=>(A j).program.rounds ()) (mem_univ j)
 unfold SmoothedMIS.LocalAlg.output
 change (A j).program.out (((parallel A).program.run G () ids inp (fun _ _=>false)
   ((parallel A).program.rounds ()) v).2 j)=_
 rw [Lb,min_eq_right hT]
end Fe
end
noncomputable section
namespace Be
def LR {n: ℕ} (i: Fin n): Fin (2*n):=⟨2*i.val,by omega⟩
def K2 {n: ℕ} (i: Fin n): Fin (2*n):=⟨2*i.val+1,by omega⟩
def KD (Rbound n: ℕ): Deterministic Unit (Fin (2*n)→ Option ℕ) (Fin n→ Option ℕ):=
 C7.transform (Fe.parallel (fun _: Fin n=>Ek Rbound))
   (fun _ inp i=>(inp (LR i),inp (K2 i))) (fun _ _ out=>out)
lemma xS (Rbound n: ℕ):(KD Rbound n).program.rounds ()≤ 2*Rbound:= by
 change (Fe.parallel (fun _: Fin n=>Ek Rbound)).program.rounds ()≤ 2*Rbound
 exact Fe.Ma (fun _: Fin n=>Ek Rbound) (2*Rbound) (fun _=>le_rfl)
lemma xR {N n: ℕ} (G: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (inp: Fin N→ Fin (2*n)→ Option ℕ) (Rbound: ℕ) (v: Fin N) (i: Fin n):
   execute (KD Rbound n) G () ids inp v i=
     execute (Ek Rbound) G () ids
       (fun w=>(inp w (LR i),inp w (K2 i))) v:= by
 unfold execute KD
 rw [C7.A4]
 exact Fe.Gn _ G ids (fun w i=>(inp w (LR i),inp w (K2 i))) v i
lemma uT {N n: ℕ} (G: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (hi: Function.Injective ids) (inp: Fin N→ Fin (2*n)→ Option ℕ)
   (M: Fin (2*n)→ SimpleGraph (Fin N))
   (hM:∀i,ReportsMatching G ids (fun v=>inp v i) (M i)) (r: ℕ):
   ∃J: Fin n→ SimpleGraph (Fin N),∀i,
     ReportsMatching G ids (fun v=>execute (KD (2*r+2) n) G () ids inp v i) (J i)∧
     r*matchingSize (M (LR i))≤(r+2)*matchingSize (J i)∧
     r*matchingSize (M (K2 i))≤(r+2)*matchingSize (J i):= by
 have hPair (i: Fin n):=k0 G (M (LR i)) (M (K2 i)) ids hi
   (fun v=>inp v (LR i)) (fun v=>inp v (K2 i)) (hM _) (hM _) r
 let J: Fin n→ SimpleGraph (Fin N):=fun i=>(hPair i).choose
 refine ⟨J,?_⟩
 intro i
 have hSpec:=(hPair i).choose_spec
 refine ⟨?_,hSpec.2⟩
 simpa only [xR] using hSpec.1
end Be
end
noncomputable section
namespace Be
@[reducible] def Jp: ℕ→ ℕ
 | 0=>1
 | d+1=>2*Jp d
lemma uS (d: ℕ): Jp d=2^d:= by induction d<;> simp_all [Jp,pow_succ,mul_comm]
def LX (Rbound: ℕ):(d: ℕ)→ Deterministic Unit (Fin (Jp d)→ Option ℕ) (Option ℕ)
 | 0=>C7.pointwise (fun _ inp=>inp ⟨0,by decide⟩)
 | d+1=>Ff.sequence (KD Rbound (Jp d)) (LX Rbound d) (fun _ _ _ out=>out)
lemma Ap (Rbound d: ℕ):(LX Rbound d).program.rounds ()≤ d*(2*Rbound+1):= by
 induction d with
 | zero => simp [LX,C7.pointwise]
 | succ d ih =>
   change (KD Rbound (Jp d)).program.rounds ()+1+(LX Rbound d).program.rounds ()≤ _
   have hLevel:=xS Rbound (Jp d)
   nlinarith
lemma Hk (n: ℕ) (k: Fin (2*n)):∃i: Fin n,k=LR i∨ k=K2 i:= by
 let i: Fin n:=⟨k.val/2,by have h:=k.isLt;omega⟩
 refine ⟨i,?_⟩
 by_cases hRem: k.val%2=0
 · left;apply Fin.ext;dsimp [i,LR];omega
 · right;apply Fin.ext;dsimp [i,K2];omega
lemma xT {N: ℕ} (G: SimpleGraph (Fin N)) (ids: Fin N→ ℕ)
   (hi: Function.Injective ids) (r d: ℕ) (inp: Fin N→ Fin (Jp d)→ Option ℕ)
   (M: Fin (Jp d)→ SimpleGraph (Fin N))
   (hM:∀i,ReportsMatching G ids (fun v=>inp v i) (M i)):
   ∃J: SimpleGraph (Fin N),
     ReportsMatching G ids (execute (LX (2*r+2) d) G () ids inp) J∧
     ∀i,r^d*matchingSize (M i)≤(r+2)^d*matchingSize J:= by
 induction d with
 | zero =>
   let z: Fin (Jp 0):=⟨0,by decide⟩
   refine ⟨M z,?_,?_⟩
   · exact hM z
   · intro i
     have hI: i=z:=by apply Fin.ext;change i.val=0;have h: i.val< 1:=i.isLt;omega
     rw [hI]
     simp
 | succ d ih =>
   obtain ⟨P,hP⟩:=uT G ids hi inp M hM r
   let mid: Fin N→ Fin (Jp d)→ Option ℕ:=
     execute (KD (2*r+2) (Jp d)) G () ids inp
   obtain ⟨J,hJ,hBound⟩:=ih mid P (fun i=>(hP i).1)
   refine ⟨J,?_,?_⟩
   · have hOutput: execute (LX (2*r+2) (d+1)) G () ids inp=
         execute (LX (2*r+2) d) G () ids mid:= by
       funext v
       unfold execute
       change (Ff.sequence _ _ _).program.output G () ids inp (fun _ _=>false) v=_
       rw [Ff.CM]
       rfl
     rw [hOutput]
     exact hJ
   · intro k
     obtain ⟨i,hChild⟩:=Hk (Jp d) k
     have hFirst: r*matchingSize (M k)≤(r+2)*matchingSize (P i):= by
       rcases hChild with hChild|hChild
       · rw [hChild];exact (hP i).2.1
       · rw [hChild];exact (hP i).2.2
     have hLeft:=Nat.mul_le_mul_left (r^d) hFirst
     have hRight:=Nat.mul_le_mul_left (r+2) (hBound i)
     rw [pow_succ,pow_succ]
     nlinarith
end Be
end
noncomputable section
namespace Be
def yZ (ell B: ℕ): ℕ:=3*AG ell*KT ell B
def JL (ell B: ℕ): ℕ:=AH ell B*yZ ell B
lemma p4 (ell B: ℕ):
   Fintype.card (Bj ell B)=(AH ell B)^yZ ell B:= by
 simp only [Bj,Fintype.card_fun,Fintype.card_fin,Fintype.card_prod]
 rw [show AH ell B*(AH ell B*AH ell B)=(AH ell B)^3 by ring,
   ←pow_mul,←pow_mul]
 congr 1
 unfold yZ
 ring
lemma jR (ell B: ℕ):
   Fintype.card (Bj ell B)≤ Jp (JL ell B):= by
 rw [p4,uS,JL,pow_mul]
 exact Nat.pow_le_pow_left (AH ell B).lt_two_pow_self.le (yZ ell B)
def I2 {α: Type} [Fintype α] (default: α) (d: ℕ)
   (i: Fin (Jp d)): α:=
 if hi: i.val<Fintype.card α then (Fintype.equivFin α).symm ⟨i.val,hi⟩ else default
lemma kE {α: Type} [Fintype α] (default: α) (d: ℕ)
   (hCard: Fintype.card α≤ Jp d): Function.Surjective (I2 default d):= by
 intro a
 let i: Fin (Jp d):=⟨(Fintype.equivFin α a).val,lt_of_lt_of_le (Fintype.equivFin α a).isLt hCard⟩
 refine ⟨i,?_⟩
 unfold I2
 rw [dif_pos (show i.val<Fintype.card α from (Fintype.equivFin α a).isLt)]
 exact (Fintype.equivFin α).symm_apply_apply a
def Lg (ell B: ℕ) (hQ: 0<AH ell B): Bj ell B:=
 fun _ _=>(⟨0,hQ⟩,⟨0,hQ⟩,⟨0,hQ⟩)
def GT (ell B: ℕ) (hQ: 0<AH ell B):
   Fin (Jp (JL ell B))→ Bj ell B:=
 I2 (Lg ell B hQ) (JL ell B)
lemma h7 (ell B: ℕ) (hQ: 0<AH ell B):
   Function.Surjective (GT ell B hQ):=
 kE _ _ (jR ell B)
lemma pL {ell B: ℕ} (hell: 0<ell) (hB: 0<B): 0<AH ell B:= by
 unfold AH AI zX AG Fn
 positivity
end Be
end
noncomputable section
namespace Be
lemma kD (x: ℝ) (hx: 0≤ x) (d: ℕ):
   2*(d: ℝ)*x≤ 1→(1+x)^d≤ 1+2*(d: ℝ)*x:= by
 induction d with
 | zero => intro h;simp
 | succ d ih =>
   intro hSmall
   norm_num only [Nat.cast_add,Nat.cast_one] at hSmall ⊢
   have hPrevSmall: 2*(d: ℝ)*x≤ 1:=by nlinarith
   have hPrev:=ih hPrevSmall
   have hMul:=mul_le_mul_of_nonneg_right hPrev (show 0≤ 1+x by linarith)
   have hCross:=mul_nonneg hx (show 0≤ 1-2*(d: ℝ)*x by linarith)
   rw [pow_succ]
   nlinarith
def Jq (q d: ℕ): ℕ:=16*q*(d+1)
lemma Cb {q: ℕ} (hq: 0< q) (d: ℕ): 0< Jq q d:= by unfold Jq;positivity
lemma uU {q: ℕ} (hq: 1≤ q) (d: ℕ):
   (1+2/(Jq q d: ℝ))^d≤ 1+1/(4*(q: ℝ)):= by
 have hqR:(1:ℝ)≤ q:=by exact_mod_cast hq
 have hR: 0<(Jq q d: ℝ):=by exact_mod_cast Cb (by omega: 0< q) d
 have hRadius:(Jq q d: ℝ)=16*(q: ℝ)*((d: ℝ)+1):=by simp [Jq]
 have hBound: 4*(d: ℝ)/(Jq q d: ℝ)≤ 1/(4*(q: ℝ)):= by
   apply (div_le_div_iff₀ hR (by positivity: 0<4*(q: ℝ))).mpr
   rw [hRadius]
   nlinarith
 have hQuarter: 1/(4*(q: ℝ))≤ 1:=(div_le_one (by positivity: 0<4*(q: ℝ))).mpr (by linarith)
 have hEq: 2*(d: ℝ)*(2/(Jq q d: ℝ))=4*(d: ℝ)/(Jq q d: ℝ):=by ring
 have hSmall: 2*(d: ℝ)*(2/(Jq q d: ℝ))≤ 1:=by rw [hEq];exact hBound.trans hQuarter
 have hPow:=kD (2/(Jq q d: ℝ)) (by positivity) d hSmall
 rw [hEq] at hPow
 linarith
lemma Aq {q d m j: ℕ} (hq: 1≤ q)
   (hTree:(Jq q d)^d*m≤(Jq q d+2)^d*j):
   (m: ℝ)≤(1+1/(4*(q: ℝ)))*(j: ℝ):= by
 have hR: 0<(Jq q d: ℝ):=by exact_mod_cast Cb (by omega: 0< q) d
 have hCast:(Jq q d: ℝ)^d*(m: ℝ)≤((Jq q d: ℝ)+2)^d*(j: ℝ):=by exact_mod_cast hTree
 have hAdd:(Jq q d: ℝ)+2=(Jq q d: ℝ)*(1+2/(Jq q d: ℝ)):= by
   field_simp
 rw [hAdd,mul_pow,mul_assoc] at hCast
 have hDiv:(m: ℝ)≤(1+2/(Jq q d: ℝ))^d*(j: ℝ):=
   (mul_le_mul_iff_right₀ (pow_pos hR d)).mp hCast
 exact hDiv.trans (mul_le_mul_of_nonneg_right (uU hq d) (by positivity))
lemma bR {q: ℕ} (hq: 1≤ q) (opt best final: ℝ)
   (hFinal: 0≤ final) (hOpt: opt≤(1+1/(4*(q: ℝ)))*best)
   (hBest: best≤(1+1/(4*(q: ℝ)))*final): opt≤(1+1/(q: ℝ))*final:= by
 have hqR:(1:ℝ)≤ q:=by exact_mod_cast hq
 have hA: 0≤ 1/(4*(q: ℝ)):=by positivity
 have hALe: 1/(4*(q: ℝ))≤ 1:=(div_le_one (by positivity: 0<4*(q: ℝ))).mpr (by linarith)
 have hFour: 4*(1/(4*(q: ℝ)))=1/(q: ℝ):=by field_simp
 have hSquare:(1+1/(4*(q: ℝ)))^2≤ 1+1/(q: ℝ):= by
   nlinarith [mul_nonneg hA (sub_nonneg.mpr hALe)]
 calc
   opt≤(1+1/(4*(q: ℝ)))*best:=hOpt
   _≤(1+1/(4*(q: ℝ)))*((1+1/(4*(q: ℝ)))*final):=
     mul_le_mul_of_nonneg_left hBest (by linarith)
   _=(1+1/(4*(q: ℝ)))^2*final:=by ring
   _≤(1+1/(q: ℝ))*final:=mul_le_mul_of_nonneg_right hSquare hFinal
end Be
end
noncomputable section
namespace Be
variable {K: Type}
def Cr (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   (ell B: ℕ) (hQ: 0<AH ell B):
   Deterministic Unit Ln (Fin (Jp (JL ell B))→ Option ℕ):=
 C7.transform
   (Fe.parallel (fun i=>I6 A k ell B (GT ell B hQ i)))
   (fun _ data _=>data) (fun _ _ outputs=>outputs)
def Dm (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   (q B: ℕ) (hQ: 0<AH (8*q) B): Deterministic Unit Ln (Option ℕ):=
 Ff.sequence (Cr A k (8*q) B hQ)
   (LX (2*Jq q (JL (8*q) B)+2) (JL (8*q) B)) (fun _ _ _ z=>z)
variable {N q B: ℕ} {G M0: SimpleGraph (Fin N)} {ids: Fin N→ ℕ}
   (hi: Function.Injective ids) (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   (hq: 2≤q) (hB: 0<B) (hOpt: optimum G≤ B*matchingSize M0)
   (hOracle: qH A k G ids (zX (8*q)) B)
   (data: Fin N→ Ln) (hNei:∀v,(data v).neighbors=neighborIDs G ids v)
   (hReports: ReportsMatching G ids (KJ data) M0)
include hi hq hB hOpt hOracle hNei hReports in
lemma j4 (hQ: 0<AH (8*q) B):
   ∃M,ReportsMatching G ids (execute (Dm A k q B hQ) G () ids data) M∧
     (optimum G: ℝ)≤(1+1/(q: ℝ))*(matchingSize M: ℝ):= by
 let d:=JL (8*q) B
 let branches:=fun i: Fin (Jp d)=>I6 A k (8*q) B (GT (8*q) B hQ i)
 let inp:=execute (Cr A k (8*q) B hQ) G () ids data
 have hThread (i: Fin (Jp d)):(fun v=>inp v i)=execute (branches i) G () ids data:=by
   funext v
   unfold inp Cr execute
   rw [C7.A4]
   exact Fe.Gn _ G ids (fun v _=>data v) v i
 have hAll:∀i: Fin (Jp d),∃M,ReportsMatching G ids (fun v=>inp v i) M:=by
   intro i
   rw [hThread]
   exact oY G ids hi A k (8*q) B _ data
 choose matchings hMatchings using hAll
 obtain ⟨σ,Mbest,hBest,hBestSize⟩:=Jd hi A k hOracle hB hOpt (by omega: 0<8*q) data hNei hReports
 obtain ⟨best,hDecode⟩:=h7 (8*q) B hQ σ
 have hBestReport: ReportsMatching G ids (fun v=>inp v best) Mbest:=by
   rw [hThread]
   change ReportsMatching G ids (execute (I6 A k (8*q) B (GT (8*q) B hQ best)) G () ids data) Mbest
   rw [hDecode]
   exact hBest
 have hBestEq: matchings best=Mbest:=by
   ext u v
   constructor
   · intro hE
     obtain ⟨w,hW,hID⟩:=(hBestReport.2 u).2 (ids v)|>.mp
       (((hMatchings best).2 u).2 (ids v)|>.mpr ⟨v,hE,rfl⟩)
     exact hi hID ▸hW
   · intro hE
     obtain ⟨w,hW,hID⟩:=((hMatchings best).2 u).2 (ids v)|>.mp
       ((hBestReport.2 u).2 (ids v)|>.mpr ⟨v,hE,rfl⟩)
     exact hi hID ▸hW
 obtain ⟨M,hM,hTree⟩:=xT G ids hi (Jq q d) d inp matchings hMatchings
 refine ⟨M,?_,?_⟩
 · have hOutput: execute (Dm A k q B hQ) G () ids data=
       execute (LX (2*Jq q d+2) d) G () ids inp:=by
     funext v
     unfold execute Dm
     rw [Ff.CM]
     rfl
   rw [hOutput]
   exact hM
 · have hQuarter:(optimum G: ℝ)≤(1+1/(4*(q: ℝ)))*(matchingSize Mbest: ℝ):=by
     have hCast:(8*(q: ℝ))*(optimum G: ℝ)≤(8*(q: ℝ)+2)*(matchingSize Mbest: ℝ):=by exact_mod_cast hBestSize
     have hQreal: 0<(q: ℝ):=by exact_mod_cast (show 0<q by omega)
     apply (mul_le_mul_iff_right₀ (by positivity: 0<8*(q: ℝ))).mp
     have hh:(8*(q: ℝ))*((1+1/(4*(q: ℝ)))*(matchingSize Mbest: ℝ))=
         (8*(q: ℝ)+2)*(matchingSize Mbest: ℝ):=by field_simp;ring
     rw [hh]
     nlinarith [hCast]
   have hBestFinal:=(Aq (by omega: 1≤q) (hTree best))
   rw [hBestEq] at hBestFinal
   exact bR (by omega) _ _ _ (by positivity) hQuarter hBestFinal
end Be
end
noncomputable section
namespace Be
def vE (ell B: ℕ): ℕ:=2+AG ell*
 (3*AH ell B*(7*zX ell+9)+5*zX ell+19)
def qV (ell B: ℕ): ℕ:=2+KT ell B*(vE ell B+1)
lemma z2 (ell B: ℕ) (σ: Bj ell B) (t i: ℕ):
   (Kj ell B σ t i).1≤AH ell B∧
   (Kj ell B σ t i).2.1≤AH ell B∧
   (Kj ell B σ t i).2.2≤AH ell B:= by
 unfold Kj
 split_ifs with ht hi
 · exact ⟨(σ ⟨t,ht⟩ ⟨i,hi⟩).1.isLt.le,(σ ⟨t,ht⟩ ⟨i,hi⟩).2.1.isLt.le,
     (σ ⟨t,ht⟩ ⟨i,hi⟩).2.2.isLt.le⟩
 · exact ⟨Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩
 · exact ⟨Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩
variable {K: Type} (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K) (ell B: ℕ)
   (σ: Bj ell B)
lemma t2 (t: ℕ):
   (If A k (zX ell) ell (Ey ell+1) (AG ell)
     (Kj ell B σ t)).program.rounds ()≤ vE ell B*(A.program.rounds k+1):= by
 let size:=zX ell
 let Q:=AH ell B
 let P:=AG ell
 let a:=A.program.rounds k
 have hWeight: 5*size+7+(2*size+2)*a≤(7*size+9)*(a+1):=by nlinarith
 have hEach:∀i∈range P,
     ((Kj ell B σ t i).1+(Kj ell B σ t i).2.1+(Kj ell B σ t i).2.2)*
       (5*size+7+(2*size+2)*a)+5*size+18≤
       (3*Q*(7*size+9)+5*size+18)*(a+1):=by
   intro i hi
   have hStops:=z2 ell B σ t i
   have hSum:(Kj ell B σ t i).1+(Kj ell B σ t i).2.1+
       (Kj ell B σ t i).2.2≤ 3*Q:=by dsimp [Q];omega
   have hh:=Nat.mul_le_mul hSum hWeight
   nlinarith
 have hTotal:=sum_le_sum hEach
 simp only [sum_const,card_range,smul_eq_mul] at hTotal
 rw [sF]
 change 1+P+_≤ _
 unfold vE
 change 1+P+_≤(2+P*(3*Q*(7*size+9)+5*size+19))*(a+1)
 nlinarith
lemma t1:(I6 A k ell B σ).program.rounds ()≤
   qV ell B*(A.program.rounds k+1):= by
 have hPhases:=sum_le_sum (fun i (_: i∈range (KT ell B))=>t2 A k ell B σ i)
 simp only [sum_const,card_range,smul_eq_mul] at hPhases
 change (I7 A k ell B σ).program.rounds ()+1+1≤ _
 rw [I7,IM.Gz]
 unfold qV
 nlinarith
end Be
end
noncomputable section
namespace Be
variable {K: Type}
def uF (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K) (ell: ℕ):
   Deterministic Unit (Finset ℕ) Ln:=
 C7.transform (C7.NE A k) (fun _ z=>z)
   (fun j neighbors out=>Ln.K8 ell j neighbors out)
def uG (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   (q B: ℕ) (hQ: 0<AH (8*q) B): Deterministic Unit (Finset ℕ) (Option ℕ):=
 Ff.sequence (uF A k (8*q)) (Dm A k q B hQ) (fun _ _ _ z=>z)
def oK (q B: ℕ): ℕ:=qV (8*q) B+3+
 JL (8*q) B*(4*Jq q (JL (8*q) B)+5)
lemma mF (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   (q B: ℕ) (hQ: 0<AH (8*q) B):
   (Dm A k q B hQ).program.rounds ()≤
     (qV (8*q) B+1+JL (8*q) B*(4*Jq q (JL (8*q) B)+5))*
       (A.program.rounds k+1):= by
 have hParallel:(Cr A k (8*q) B hQ).program.rounds ()≤
     qV (8*q) B*(A.program.rounds k+1):=by
   change (Fe.parallel (fun i=>I6 A k (8*q) B (GT (8*q) B hQ i))).program.rounds ()≤ _
   apply Fe.Ma
   intro i
   exact t1 A k (8*q) B _
 have hMerge:=Ap (2*Jq q (JL (8*q) B)+2) (JL (8*q) B)
 change (Cr A k (8*q) B hQ).program.rounds ()+1+
   (LX (2*Jq q (JL (8*q) B)+2) (JL (8*q) B)).program.rounds ()≤ _
 nlinarith
lemma fD (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   (q B: ℕ) (hQ: 0<AH (8*q) B):
   (uG A k q B hQ).program.rounds ()≤ oK q B*(A.program.rounds k+1):= by
 have hh:=mF A k q B hQ
 change A.program.rounds k+1+(Dm A k q B hQ).program.rounds ()≤ _
 unfold oK
 nlinarith
lemma fC (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K) (ell: ℕ)
   {N: ℕ} (G: SimpleGraph (Fin N)) (ids: Fin N→ ℕ) (inp: Fin N→ Finset ℕ):
   execute (uF A k ell) G () ids inp=
     fun v=>Ln.K8 ell (ids v) (inp v) (execute A G k ids inp v):= by
 funext v
 unfold execute uF
 rw [C7.A4,C7.FS]
variable {N q B: ℕ} {G: SimpleGraph (Fin N)} {ids: Fin N→ ℕ}
   (hi: Function.Injective ids) (A: Deterministic K (Finset ℕ) (Option ℕ)) (k: K)
   (hq: 2≤q) (hB: 0<B) (hQ: 0<AH (8*q) B)
   (hInitial: Ms A k G ids B)
   (hOracle: qH A k G ids (zX (8*q)) B)
include hi hq hB hInitial hOracle in
lemma d4:∃M,
   ReportsMatching G ids (execute (uG A k q B hQ) G () ids (neighborIDs G ids)) M∧
     (optimum G: ℝ)≤(1+1/(q: ℝ))*(matchingSize M: ℝ):= by
 obtain ⟨M0,hM0,hApprox⟩:=hInitial
 let data:=execute (uF A k (8*q)) G () ids (neighborIDs G ids)
 have hData:=fC A k (8*q) G ids (neighborIDs G ids)
 have hNei:∀v,(data v).neighbors=neighborIDs G ids v:=by
   intro v
   change (execute (uF A k (8*q)) G () ids (neighborIDs G ids) v).neighbors=_
   rw [hData]
   rfl
 have hReport: ReportsMatching G ids (KJ data) M0:=by
   have hh: KJ data=execute A G k ids (neighborIDs G ids):=by
     rw [show data= _ from hData]
     rfl
   rw [hh]
   exact hM0
 obtain ⟨M,hM,hSize⟩:=j4 hi A k hq hB hApprox hOracle data hNei hReport hQ
 refine ⟨M,?_,hSize⟩
 have hOutput: execute (uG A k q B hQ) G () ids (neighborIDs G ids)=
     execute (Dm A k q B hQ) G () ids data:=by
   funext v
   unfold execute uG
   rw [Ff.CM]
   rfl
 rw [hOutput]
 exact hM
end Be
end
noncomputable section
namespace Be
def DW (p: ℕ) (k: Bounds) (q: ℕ): Bounds:=
 ⟨(k.n+1)*(q+1)^p,(k.degree+1)*(q+1)^p⟩
lemma z7 {N n n' a a': ℕ} {ids: Fin N→ ℕ}
   (h: Identifiers n a ids) (hn: n≤n') (ha: a≤a'): Identifiers n' a' ids:= by
 refine ⟨h.1,?_⟩
 intro v
 exact (h.2 v).trans_le ((Nat.pow_le_pow_left (max_le_max_left 2 hn) a).trans
   (Nat.pow_le_pow_right (by omega: 0< max 2 n') ha))
lemma FZ (p: ℕ) (k: Bounds) (q: ℕ): k.n≤(DW p k q).n:= by
 have hp: 0<(q+1)^p:=pow_pos (by omega) _
 change k.n≤(k.n+1)*(q+1)^p
 nlinarith
lemma DX {N: ℕ} {G: SimpleGraph (Fin N)} {k: Bounds} (p q: ℕ)
   (hG: boundedGraph G k.n k.degree):
   boundedGraph G (DW p k q).n (DW p k q).degree:= by
 have hp: 0<(q+1)^p:=pow_pos (by omega) _
 refine ⟨hG.1.trans (FZ p k q),?_⟩
 intro v
 exact (hG.2 v).trans (by change k.degree≤(k.degree+1)*(q+1)^p;nlinarith)
lemma uC {N size: ℕ} {G: SimpleGraph (Fin N)} {k: Bounds} (p q: ℕ)
   (hG: boundedGraph G k.n k.degree) (hSize: size≤(q+1)^p)
   (P: tE G size) (Lx: Fin N→ Fin N→ Prop) (hC: Symmetric Lx):
   boundedGraph (P.Lv Lx hC) (DW p k q).n (DW p k q).degree:= by
 refine ⟨hG.1.trans (FZ p k q),?_⟩
 intro v
 exact (P.zR Lx hC k.degree hG.2 v).trans (by
   change size*k.degree≤(k.degree+1)*(q+1)^p
   have hh:=Nat.mul_le_mul_right k.degree hSize
   nlinarith)
lemma iT (c: ℝ) (hc: 0<c):∃B: ℕ,0<B∧
   ∀opt m: ℕ,c*(opt: ℝ)≤(m: ℝ)→ opt≤B*m:= by
 obtain ⟨B,hB⟩:=exists_nat_ge (1/c)
 refine ⟨B+1,by omega,?_⟩
 intro opt m hApprox
 have hC: 1≤c*((B+1: ℕ): ℝ):=by
   have hh:=mul_le_mul_of_nonneg_left hB hc.le
   rw [mul_one_div_cancel hc.ne'] at hh
   push_cast
   nlinarith
 have hM:=mul_le_mul_of_nonneg_left hApprox (show 0≤((B+1: ℕ): ℝ) by positivity)
 have hOpt:=mul_le_mul_of_nonneg_right hC (show 0≤(opt: ℝ) by positivity)
 have hh:(opt: ℝ)≤((B+1: ℕ): ℝ)*(m: ℝ):=by nlinarith
 exact_mod_cast hh
end Be
end
noncomputable section
namespace Be
def Bq (A: Deterministic Bounds (Finset ℕ) (Option ℕ)) (p B: ℕ) (hB: 0<B)
   (input: Bounds ×ℕ): Deterministic Unit (Finset ℕ) (Option ℕ):=
 if hq: 2≤ input.2 then
   uG A (DW p input.1 input.2) input.2 B
     (pL (by omega: 0<8*input.2) hB)
 else C7.pointwise (fun _ _=>none)
def Kn (A: Deterministic Bounds (Finset ℕ) (Option ℕ)) (p B: ℕ) (hB: 0<B):
   Deterministic (Bounds ×ℕ) (Finset ℕ) (Option ℕ):=
 IL.select (Bq A p B hB)
lemma w3 (A: Deterministic Bounds (Finset ℕ) (Option ℕ)) (p B: ℕ) (hB: 0<B)
   {N: ℕ} (G: SimpleGraph (Fin N)) (k: Bounds) (q: ℕ) (hq: 2≤q)
   (ids: Fin N→ ℕ) (inp: Fin N→ Finset ℕ):
   execute (Kn A p B hB) G (k,q) ids inp=
     execute (uG A (DW p k q) q B
       (pL (by omega: 0<8*q) hB)) G () ids inp:= by
 funext v
 unfold execute Kn
 rw [IL.GG]
 unfold Bq
 rw [dif_pos hq]
lemma w4 (A: Deterministic Bounds (Finset ℕ) (Option ℕ)) (p B C: ℕ) (hB: 0<B)
   (hRuntime:∀q: ℕ,2≤q→ oK q B≤ C*(q+1)^p)
   (k: Bounds) (q: ℕ) (hq: 2≤q):
   (Kn A p B hB).program.rounds (k,q)≤
     C*(q+1)^p*(A.program.rounds (DW p k q)+(q+1)^p):= by
 change (Bq A p B hB (k,q)).program.rounds ()≤ _
 unfold Bq
 rw [dif_pos hq]
 have hRound:=fD A (DW p k q) q B
   (pL (by omega: 0<8*q) hB)
 have hPow: 1≤(q+1)^p:=by have hh:0<(q+1)^p:=pow_pos (by omega) _;omega
 exact hRound.trans (Nat.mul_le_mul (hRuntime q hq) (Nat.add_le_add_left hPow _))
end Be
end
namespace Be
def tH (f: ℕ→ ℕ): Prop:=∃C p: ℕ,∀q: ℕ,f q≤ C*(q+1)^p
namespace tH
lemma const (c: ℕ): tH (fun _=>c):=⟨c,0,by intro q;simp⟩
lemma identity: tH (fun q=>q):=⟨1,1,by intro q;simp⟩
lemma add {f g: ℕ→ ℕ} (hf: tH f) (hg: tH g):
   tH (fun q=>f q+g q):= by
 obtain ⟨C,p,hC⟩:=hf
 obtain ⟨D,r,hD⟩:=hg
 refine ⟨C+D,p+r,?_⟩
 intro q
 have hp: 0<(q+1)^p:=pow_pos (by omega) _
 have hr: 0<(q+1)^r:=pow_pos (by omega) _
 have hCP:=hC q
 have hDQ:=hD q
 rw [pow_add]
 nlinarith [Nat.mul_le_mul_left (C*(q+1)^p) (show 1≤(q+1)^r by omega),
   Nat.mul_le_mul_left (D*(q+1)^r) (show 1≤(q+1)^p by omega)]
lemma mul {f g: ℕ→ ℕ} (hf: tH f) (hg: tH g):
   tH (fun q=>f q*g q):= by
 obtain ⟨C,p,hC⟩:=hf
 obtain ⟨D,r,hD⟩:=hg
 refine ⟨C*D,p+r,?_⟩
 intro q
 calc
   f q*g q≤(C*(q+1)^p)*(D*(q+1)^r):=Nat.mul_le_mul (hC q) (hD q)
   _=(C*D)*(q+1)^(p+r):=by rw [pow_add];ring
end tH
end Be
noncomputable section
namespace Be
lemma CN: tH (fun q=>zX (8*q)):= by
 unfold zX AG Ey Fn
 repeat' first
   | exact tH.identity
   | exact tH.const _
   | apply tH.add
   | apply tH.mul
lemma vU (B: ℕ): tH (fun q=>oK q B):= by
 have hq:= tH.identity
 have hB:= tH.const B
 have hEll: tH (fun q=>8*q):=
   (tH.mul (tH.const 8) hq)
 have hActive: tH (fun q=>Fn (8*q)):=
   (tH.mul (tH.mul (tH.mul (tH.const 2) hEll) (tH.add hEll (tH.const 2))) (tH.add (tH.mul (tH.const 2) hEll) (tH.const 1)))
 have hHold: tH (fun q=>Ey (8*q)):=
   (tH.mul (tH.const 16) hActive)
 have hBundles: tH (fun q=>AG (8*q)):=
   (tH.mul (tH.mul (tH.mul (tH.const 16) hEll) (tH.add hEll (tH.const 1))) hActive)
 have hSize: tH (fun q=>zX (8*q)):=
   (tH.add (tH.const 2) (tH.mul hBundles (tH.mul (tH.add hHold (tH.const 1)) hEll)))
 have hGain: tH (fun q=>cW (8*q)):=
   (tH.mul (tH.mul (tH.mul (tH.const 4) hEll) (tH.add hEll (tH.const 2))) hSize)
 have hSweep: tH (fun q=>AI (8*q)):=
   (tH.mul (tH.mul (tH.mul (tH.const 4) hEll) (tH.add hEll (tH.const 2))) hBundles)
 have hCount: tH (fun q=>AH (8*q) B):=
   (tH.mul (tH.mul (tH.mul (tH.const 3) hSweep) (tH.mul (tH.mul (tH.const 2) hSize) hB)) (tH.add (tH.mul (tH.const 2) hEll) hB))
 have hPhases: tH (fun q=>KT (8*q) B):=
   (tH.mul hB hGain)
 have hCoordinates: tH (fun q=>yZ (8*q) B):=
   (tH.mul (tH.mul (tH.const 3) hBundles) hPhases)
 have hDepth: tH (fun q=>JL (8*q) B):=
   (tH.mul hCount hCoordinates)
 have hPhaseTime: tH (fun q=>vE (8*q) B):=
   (tH.add (tH.const 2) (tH.mul hBundles (tH.add (tH.add (tH.mul (tH.mul (tH.const 3) hCount) (tH.add (tH.mul (tH.const 7) hSize) (tH.const 9))) (tH.mul (tH.const 5) hSize)) (tH.const 19))))
 have hBranchTime: tH (fun q=>qV (8*q) B):=
   (tH.add (tH.const 2) (tH.mul hPhases (tH.add hPhaseTime (tH.const 1))))
 have hMerge: tH (fun q=>Jq q (JL (8*q) B)):=
   (tH.mul (tH.mul (tH.const 16) hq) (tH.add hDepth (tH.const 1)))
 exact (tH.add (tH.add hBranchTime (tH.const 3)) (tH.mul hDepth (tH.add (tH.mul (tH.const 4) hMerge) (tH.const 5))))
lemma yC (B: ℕ):∃p C: ℕ,1≤p∧ 0<C∧
   ∀q: ℕ,2≤q→ zX (8*q)≤(q+1)^p∧
     oK q B≤ C*(q+1)^p:= by
 obtain ⟨D,r,hSize⟩:=CN
 obtain ⟨E,s,hRuntime⟩:=vU B
 let p:=D+r+s+1
 refine ⟨p,E+1,by dsimp [p];omega,by omega,?_⟩
 intro q hq
 have hBase: 1≤q+1:=by omega
 have hD: D≤(q+1)^D:=(D.lt_two_pow_self.le).trans (Nat.pow_le_pow_left (by omega: 2≤q+1) D)
 have hPowDR:(q+1)^(D+r)≤(q+1)^p:=Nat.pow_le_pow_right (by omega) (by dsimp [p];omega)
 have hPowS:(q+1)^s≤(q+1)^p:=Nat.pow_le_pow_right (by omega) (by dsimp [p];omega)
 constructor
 · calc
     zX (8*q)≤ D*(q+1)^r:=hSize q
     _≤(q+1)^D*(q+1)^r:=Nat.mul_le_mul_right _ hD
     _=(q+1)^(D+r):=(pow_add _ _ _).symm
     _≤(q+1)^p:=hPowDR
 · exact (hRuntime q).trans (Nat.mul_le_mul (by omega) hPowS)
end Be
end
noncomputable section
theorem solution:
   ∀c: ℝ,0< c→ c≤ 1→
     ∃p C: ℕ,1≤ p∧ 0< C∧
       ∀(b: ℕ) (A: Deterministic Bounds (Finset ℕ) (Option ℕ)),
         (∀(N: ℕ) (G: SimpleGraph (Fin N)) (k: Bounds),
           boundedGraph G k.n k.degree→
           ∀ids: Fin N→ ℕ,Identifiers k.n (b+4) ids→
             ∃M: SimpleGraph (Fin N),
               ReportsMatching G ids (execute A G k ids (neighborIDs G ids)) M∧
               c*(optimum G:ℝ)≤(matchingSize M:ℝ))→
         ∃B: Deterministic (Bounds ×ℕ) (Finset ℕ) (Option ℕ),
           (∀(k: Bounds) (q: ℕ),2≤ q→
             B.program.rounds (k,q)≤ C*(q+1)^p*
               (A.program.rounds ⟨(k.n+1)*(q+1)^p,(k.degree+1)*(q+1)^p⟩+(q+1)^p))∧
           ∀(N: ℕ) (G: SimpleGraph (Fin N)) (k: Bounds) (q: ℕ),
             2≤ q→ boundedGraph G k.n k.degree→
             ∀ids: Fin N→ ℕ,Identifiers k.n (b+1) ids→
               ∃M: SimpleGraph (Fin N),
                 ReportsMatching G ids (execute B G (k,q) ids (neighborIDs G ids)) M∧
                 (optimum G:ℝ)≤(1+1/(q:ℝ))*(matchingSize M:ℝ):= by
 intro c hc hcOne
 obtain ⟨factor,hFactor,hInteger⟩:=Be.iT c hc
 obtain ⟨p,C,hP,hC,hBudget⟩:=Be.yC factor
 refine ⟨p,C,hP,hC,?_⟩
 intro b A hA
 refine ⟨Be.Kn A p factor hFactor,?_,?_⟩
 · intro k q hq
   exact Be.w4 A p factor C hFactor (fun q hq=>(hBudget q hq).2) k q hq
 · intro N G k q hq hGraph ids hIDs
   let inflated:=Be.DW p k q
   have hIdentifiers: Identifiers inflated.n (b+4) ids:=Be.z7 hIDs
     (Be.FZ p k q) (by omega)
   have hInitial: Be.Ms A inflated G ids factor:=by
     obtain ⟨M,hReports,hApprox⟩:=hA N G inflated (Be.DX p q hGraph) ids hIdentifiers
     exact ⟨M,hReports,hInteger (optimum G) (matchingSize M) hApprox⟩
   have hOracle: Be.qH A inflated G ids
       (Be.zX (8*q)) factor:=by
     intro P data ell mode
     obtain ⟨M,hReports,hApprox⟩:=hA N _ inflated
       (Be.uC p q hGraph (hBudget q hq).1 P
         (P.Lx ids data (Be.IO.Fz ell mode))
         (P.Dr ids data (Be.IO.Fz ell mode))) ids hIdentifiers
     exact ⟨M,hReports,hInteger _ _ hApprox⟩
   rw [Be.w3 A p factor hFactor G k q hq ids (neighborIDs G ids)]
   exact Be.d4 hIDs.1 A inflated hq hFactor
     (Be.pL (by omega: 0<8*q) hFactor) hInitial hOracle
end
