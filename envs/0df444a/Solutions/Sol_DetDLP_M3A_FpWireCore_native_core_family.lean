-- Prove2me | solution 1 for DetDLP.M3A.FpWireCore.native_core_family
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T21:33:22.100391+00:00
-- url     : https://prove2.me/submissions/fa774c68-b3d3-4017-9888-db1fbbaa631c

import Definitions.Def_DetDLP_M3A_FpWireCore

set_option autoImplicit false
namespace DetDLP.M3A.FpWireCore
open S8J S8L.FpPair.Stage FpArithNet FpChainBijection
open M3B.ECLayout (vertex port read_accepted gateSlots)
attribute [-simp] Fin.natAdd_eq_addNat
set_option backward.isDefEq.respectTransparency false

variable {p m d k T : ℕ} [Fact p.Prime]

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

theorem query_injective (q : w3_Query) (hq : w3_fpQueries q) (i : Fin q.m) : Function.Injective (q.addr i) := by
  obtain ⟨p,hp,h67,hn,h64,h4096,seed,F,hF,P,y,pre,rfl⟩ := hq
  exact hash_injective seed F i (hF i).1

theorem edges (hd : 1 ≤ d) (pre : List Bool) (prec : ℕ) : 2*(layout hd m k pre).ne ≤ budget m d k prec := by
  have := edge_budget (m:=m) (k:=k) hd pre; unfold budget; omega

variable (F : Fin m → List (ZMod p)ˣ) (seed : FpSeed p m) (P : (ZMod p)ˣ) (pre : List Bool)
variable {M : ℕ} (nz : NeZero M) (y : w3_Label M (w3_fpFB F).totalCoords) (input : List Bool)
local notation "Q" => native F seed P pre nz y input d k
variable (hd : 1 ≤ d) (hp : 2 ≤ p) (hf : p < 2^d) (ht : T ≤ 2^k) (hm : 1 ≤ m)
variable (hF : ∀ i, (F i).Nodup ∧ (F i).toFinset = fpFactorBlock T seed i) (mul : w3_modMulInterface)
local notation "A" => arith hd m k pre
local notation "f" => bus (m:=m) (k:=k) hd pre
local notation "G" => w3_factorGraph (layout hd m k pre)
local notation "sl" => gateSlots (q:=Q) A f (numbering m)

/-- Fixed-constant constructor: all address, equivalence, lookup, and incidence obligations
    are discharged. The remaining inputs are exactly the quantitative estimates. -/
noncomputable def core {C : ℕ} (shape : Shape Q C (budget m d k (w3_precision Q)))
    (deg : ∀ v ∉ w3_incLookups (layout hd m k pre) sl, (G).deg v ≤ C*Nat.ceil ((d:ℝ)^((3:ℝ)/4)))
    (eqdeg : 2 ≤ C*Nat.ceil ((d:ℝ)^((3:ℝ)/4))) : {W : w3_WireCore Q C // W.desc=(Q).input} := by
  let D := netEquiv (k:=k) hd F mul hp hf seed hF P pre hm
  have pos (i j b) : (sl).symm (.inl (i,j,b)) = Fin.natAdd (A).ng (row b i j) := rfl
  have verts (i j b) : (w3_incSlot (layout hd m k pre) sl).symm (.inl (i,j,b)) = vertex A f (row b i j) := rfl
  refine ⟨w3_incCore (q:=Q) _ sl (test hd p T (P : ZMod p).val seed pre) D (address A f) (fun i => hash_injective seed F i (hF i).1) ?_
    (fun t => (lookup_degree hd pre (row t.2.2 t.1 t.2.1))) (edges hd pre _) deg eqdeg shape,rfl⟩
  intro a i j b; change address A f (vertex A f (row b i j)) _ = _
  rw [address_at]; have H := bus_address hd F mul hp hf seed hF P pre hm ht (w3_factorEquiv _ _ a) b i j
  have L := funext fun u => read_accepted A f (arithTest hd p T (P : ZMod p).val seed pre) a (row b i j) u
  cases b <;> exact (congrArg bitsToNat L).trans H

private theorem ceil_pos (d : ℕ) (hd : 1 ≤ d) : 1 ≤ Nat.ceil ((d:ℝ)^((3:ℝ)/4)) := by
  apply Nat.ceil_pos.mpr; exact Real.rpow_pos_of_pos (by exact_mod_cast hd) _

section Degrees
private theorem append_degree {n m t : ℕ} (g : Fin n → Fin t) (h : Fin m → Fin t) (v : Fin t) :
    degreeOf (Fin.addCases g h) v = degreeOf g v + degreeOf h v := by
  have split : List.finRange (n+m) = (List.finRange n).map (Fin.castAdd m) ++ (List.finRange m).map (Fin.natAdd n) := by
    apply List.ext_getElem <;> simp
    intro i hi; by_cases H : i<n
    · rw [List.getElem_append_left (by simpa using H)]; simp
    · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt H)];apply Fin.ext;simp;omega
  simp [degreeOf,split,List.filter_map,Function.comp_def]
private theorem inj_degree {n m : ℕ} (g : Fin n → Fin m) (h : Function.Injective g) (v : Fin m) : degreeOf g v ≤ 1 := by
  letI : Subsingleton {i // g i=v} := ⟨fun a b => Subtype.ext (h (a.prop.trans b.prop.symm))⟩
  have e : degreeOf g v = Fintype.card {i // g i=v} := by
    rw [Fintype.card_subtype,degreeOf,← List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _)]; congr 1;ext;simp
  rw [e];exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance

/-- An injectively wired lookup bus costs each arithmetic bit at most one incidence. -/
theorem bit_degree (pre : List Bool) (v : Fin (arith hd m k pre).nb) :
    (w3_factorGraph (layout hd m k pre)).deg (Fin.natAdd _ v) ≤ (w3_factorGraph (arith hd m k pre)).deg (Fin.natAdd _ v)+1 := by
  rw [w3_bitDegree,w3_bitDegree]; change degreeOf (Fin.addCases (arith hd m k pre).bit (fun e => bus hd pre (M3B.ECLayout.row e) (M3B.ECLayout.column e))) v ≤ _
  rw [append_degree]; apply Nat.add_le_add_left; apply inj_degree; intro a b e; apply finProdFinEquiv.symm.injective
  exact bus_injective hd pre e

/-- Ordinary gate degrees do not change; only the bit bound pays the extra incidence. -/
theorem core_degree {D : ℕ} (bound : ∀ v, (w3_factorGraph A).deg v ≤ D) (v : Fin (G).nV) (hv : v ∉ w3_incLookups (layout hd m k pre) sl) : (G).deg v ≤ D+1 := by
  induction v using Fin.addCases with
  | left g => induction g using Fin.addCases with
    | left g => exact (M3B.ECLayout.ordinary_degree A f g).le.trans ((bound _).trans (Nat.le_succ _))
    | right s => exfalso; apply hv; apply Finset.mem_image.mpr; obtain ⟨b,i,j,rfl⟩ := row_surj s; exact ⟨(i,j,b),Finset.mem_univ _,rfl⟩
  | right v => exact (bit_degree hd pre v).trans (Nat.succ_le_succ (bound _))
end Degrees

private theorem count_sq (d : ℕ) (hd : 2 ≤ d) : blockCount d * blockCount d ≤ 16*d := by
  let a := Nat.clog 2 (d+2)
  have ha : 1 ≤ a := Nat.clog_pos (by decide) (by omega)
  have hr := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast ha : (1:ℝ) ≤ a) (by norm_num : (1:ℝ)/4 ≤ 1/2)
  rw [← Real.sqrt_eq_rpow] at hr
  have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ (a:ℝ)^((1:ℝ)/4))
  have hs : 1 ≤ Real.sqrt (a:ℝ) := by exact (Real.le_sqrt_of_sq_le (by simpa using (show (1:ℝ) ≤ a by exact_mod_cast ha)))
  have hh : (blockCount d:ℝ) ≤ 2*Real.sqrt (a:ℝ) := by unfold blockCount; push_cast; exact max_le (by linarith) (by change (⌈(a:ℝ)^((1:ℝ)/4)⌉₊:ℝ) ≤ _;linarith)
  have hq := mul_self_le_mul_self (Nat.cast_nonneg (blockCount d)) hh
  have hav : a ≤ d+2 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
  have H : (blockCount d:ℝ)*(blockCount d:ℝ) ≤ 16*d := by nlinarith [Real.sq_sqrt (Nat.cast_nonneg a), (show (a:ℝ) ≤ d+2 by exact_mod_cast hav), (show (2:ℝ) ≤ d by exact_mod_cast hd)]
  exact_mod_cast H

private theorem width_bounds {p : ℕ} (hp : 67 < p) (d : ℕ) (hd : d=bitLen p) (hd2 : 2 ≤ d) :
    let m := blockCount d; let T := hashThreshold p (p-1) m (p-1); let k := Nat.clog 2 (2*T)
    4*m*k ≤ 1200*d ∧ d ≤ 4*m*k := by
  intro m T k; let n := p-1; let e := (d+4)/m+1
  have hm : 0 < m := (by decide : 1 ≤ 2).trans (le_max_left ..)
  have hn : 0 < n := by dsimp [n];omega
  have he : d+4 ≤ e*m := by dsimp [e];have a := Nat.mod_lt (d+4) hm; have b := Nat.mod_add_div (d+4) m; nlinarith only [a,b]
  have hpfit : p ≤ 2^d := hd ▸ Nat.le_pow_clog (by decide) p
  have hpow : 16*n ≤ (2^e)^m := by rw [← pow_mul]; exact (show 16*n ≤ 2^(d+4) by rw [pow_add];norm_num;dsimp [n];omega).trans (Nat.pow_le_pow_right (by decide) he)
  have root : ⌈(16*(n:ℝ))^((1:ℝ)/m)⌉₊ ≤ 2^e := by rw [Nat.ceil_le,one_div,Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity) (by exact_mod_cast hm),Real.rpow_natCast];exact_mod_cast hpow
  have qq : qStar m n ≤ 2^(12+m+e) := by
    apply max_le
    · apply (Nat.mul_le_mul_left 4096 (Nat.lt_two_pow_self (n:=m)).le).trans
      rw [pow_add,pow_add]; exact Nat.le_mul_of_pos_right _ (by positivity)
    · exact root.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have tq : T ≤ 2*qStar m n := by
    apply Nat.ceil_le.mpr; apply (div_le_iff₀ (by exact_mod_cast hn : 0 < (n:ℝ))).mpr
    change (p:ℝ)*(qStar m n:ℝ) ≤ ((2*qStar m n:ℕ):ℝ)*n; push_cast
    have h : (p:ℝ) ≤ 2*n := by exact_mod_cast (show p ≤ 2*n by dsimp [n];omega)
    nlinarith [mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (qStar m n))]
  have hk : k ≤ 14+m+e := Nat.clog_le_of_le_pow (by rw [show 14+m+e=12+m+e+2 by omega,pow_add];omega)
  have lb : 16*n ≤ (qStar m n)^m := by
    have h : (16*(n:ℝ))^((1:ℝ)/m) ≤ (qStar m n:ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right ..))
    rw [one_div,Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity) (by exact_mod_cast hm),Real.rpow_natCast] at h;exact_mod_cast h
  have qT : qStar m n ≤ T := by
    apply (Nat.cast_le (α:=ℝ)).mp; apply le_trans _ (Nat.le_ceil _); apply (le_div_iff₀ (by exact_mod_cast hn : 0 < (n:ℝ))).mpr; have h : (n:ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (qStar m n))
  have L : d ≤ k*m := by rw [hd]; apply Nat.clog_le_of_le_pow; rw [pow_mul]; exact (show p ≤ 16*n by dsimp [n];omega).trans (lb.trans (Nat.pow_le_pow_left (qT.trans ((by omega : T ≤ 2*T).trans (Nat.le_pow_clog (by decide) _))) _))
  have sq : m*m ≤ 16*d := count_sq d hd2
  have md : m ≤ 16*d := (Nat.le_mul_of_pos_right m hm).trans sq
  have tail : e*m ≤ d+4+m := by dsimp [e];rw [Nat.add_mul,one_mul];exact Nat.add_le_add_right (Nat.div_mul_le_self ..) _
  constructor <;> nlinarith only [Nat.mul_le_mul_right m hk,md,sq,tail,hd2,L]

theorem query_shape (q : w3_Query) (hq : w3_fpQueries q) : Shape q 1000000 (budget q.m q.b q.k (w3_precision q)) := by
  obtain ⟨p,prime,h67,nz,h64,h4096,seed,F,hF,P,y,pre,rfl⟩ := hq
  let d := bitLen p; let m := blockCount d; let T := hashThreshold p (p-1) m (p-1); let k := Nat.clog 2 (2*T)
  have hd : 2 ≤ d := by by_contra! h; have he := Nat.pow_le_pow_right (by decide : 0<2) (show bitLen p ≤ 1 by change d ≤ 1;omega);have := (w3_fpPrimeFits prime.out (by omega : 2<p)).2;norm_num at he;omega
  have hm : 1 ≤ m := (by decide : 1 ≤ 2).trans (le_max_left ..)
  obtain ⟨up,lo⟩ : 4*m*k ≤ 1200*d ∧ d ≤ 4*m*k := width_bounds h67 d rfl hd
  have hk : 1 ≤ k := by
    by_contra! h
    have he : k=0 := by omega
    rw [he,Nat.mul_zero] at lo;omega
  have md : m ≤ 16*d := (Nat.le_mul_of_pos_right m hm).trans (count_sq d hd)
  have pfit : p ≤ 2^d := Nat.le_pow_clog (by decide) _
  have hlog : Nat.clog 2 (2*(2*m)*(p-1)+2) ≤ 2*d+7 := by
    apply Nat.clog_le_of_le_pow; rw [show 2*d+7=d+d+7 by omega,pow_add,pow_add]; norm_num
    have h1 : m ≤ 16*2^d := md.trans (Nat.mul_le_mul_left _ (Nat.lt_two_pow_self.le))
    have h2 : p-1 ≤ 2^d := (Nat.sub_le ..).trans pfit
    nlinarith only [Nat.mul_le_mul h1 h2,Nat.two_pow_pos d,sq_nonneg (2^d:ℤ)]
  let prec := 2+4*m*k+(4*(2*m)+2)*Nat.clog 2 (2*(2*m)*(p-1)+2)
  have cover : d ≤ m*d := Nat.le_mul_of_pos_left _ hm
  have cover' : m ≤ m*d := Nat.le_mul_of_pos_right _ (by omega)
  have hp' : prec ≤ 2000*m*d := by dsimp [prec];nlinarith only [Nat.mul_le_mul_left (4*(2*m)+2) hlog,up,cover,cover',hd]
  change 2 ≤ d ∧ 1 ≤ m ∧ 1 ≤ k ∧ m ≤ 1000000*m ∧ m ≤ 1000000*m ∧ budget m d k prec ≤ 1000000*m*d ∧ 4*m*k ≤ 1000000*d ∧ d ≤ 1000000*(4*m*k) ∧ 1 ≤ prec ∧ prec ≤ budget m d k prec ∧ 1 ≤ 4*(2*m)+2+1 ∧ 4*(2*m)+2+1 ≤ 1000000*m
  have prec_pos : 1 ≤ prec := by dsimp [prec];omega
  unfold budget; refine ⟨hd,hm,hk,by omega,by omega,?_,by omega,by omega,prec_pos,by omega,by omega,by omega⟩
  nlinarith only [up,cover,cover',hp',hd]

open S8G.FpMoment S8C S8G.FpPhysicalAtom S8L.FpPair S8L.FpPair.Stage.Links w4_M5PortTensor FpSlotTile
private theorem fiber_card {n m : ℕ} (g : Fin n → Fin m) (v) : degreeOf g v = Fintype.card {i // g i=v} := by
  rw [Fintype.card_subtype,degreeOf,← List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _)];congr 1;ext;simp
private theorem bucket {n m z : ℕ} (g : Fin n → Fin m) (tag : Fin n → Fin z) (h : ∀ a b, tag a=tag b → g a=g b → a=b) (v) : degreeOf g v ≤ z := by
  rw [fiber_card]; simpa using Fintype.card_le_of_injective (fun i : {i // g i=v} => tag i.val) (fun a b e => Subtype.ext (h _ _ e (a.prop.trans b.prop.symm)))
private theorem rect {n w m : ℕ} (g : Fin (n*w) → Fin m) (h : ∀ i : Fin n, Function.Injective (fun j : Fin w => g (finProdFinEquiv (i,j)))) (v) : degreeOf g v ≤ n := by
  apply bucket g (fun u => (finProdFinEquiv.symm u).1); rintro a b; obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective a; obtain ⟨⟨l,u⟩,rfl⟩ := finProdFinEquiv.surjective b
  simp only [Equiv.symm_apply_apply]; rintro rfl e;rw [h i e]
private theorem tile_degree {m a b : ℕ} (g : Fin a → Fin b) (i : Fin m) (j : Fin b) : degreeOf (tileMap g) (finProdFinEquiv (i,j)) ≤ degreeOf g j := by
  rw [fiber_card,fiber_card]; apply Fintype.card_le_of_injective (fun u => ⟨(finProdFinEquiv.symm u.val).2,congrArg Prod.snd (finProdFinEquiv.injective u.prop)⟩)
  intro x y e; apply Subtype.ext; apply finProdFinEquiv.symm.injective;apply Prod.ext _ (congrArg Subtype.val e)
  exact (congrArg Prod.fst (finProdFinEquiv.injective x.prop)).trans (congrArg Prod.fst (finProdFinEquiv.injective y.prop)).symm
private abbrev Sh (Lyt : w3_FactorLayout) (d B : ℕ) := S8J.Shape Lyt (HashGateLayout.degreeCap d) B
private theorem tiled {Lyt : w3_FactorLayout} {B : ℕ} (h : Sh Lyt d B) (m : ℕ) : Sh (tiles m Lyt) d B := by
  constructor <;> intro i <;> obtain ⟨⟨s,j⟩,rfl⟩ := finProdFinEquiv.surjective i
  · exact (Nat.cast_le.mpr (tile_degree Lyt.gate s j)).trans_lt (h.1 j)
  · exact (tile_degree Lyt.bit s j).trans (h.2 j)
private theorem widen {Lyt : w3_FactorLayout} {b c : ℕ} (h : Sh Lyt d b) (e : b ≤ c) : Sh Lyt d c := ⟨h.1,fun i => (h.2 i).trans e⟩
private theorem link_sh {Lyt : w3_FactorLayout} {b n L R : ℕ} {l r : Fin n → Fin Lyt.nb} (h : Sh Lyt d b) (hl : ∀ i, degreeOf l i ≤ L) (hr : ∀ i, degreeOf r i ≤ R) : Sh (links Lyt l r) d (b+L+R) := by
  constructor
  · intro i; induction i using Fin.addCases with
    | left g => change (degreeOf (splitMap Lyt.gate (Fin.addCases id id)) (Fin.castAdd n g):ℝ) < _;rw [degree_left];exact h.1 g
    | right i => change (degreeOf (splitMap Lyt.gate (Fin.addCases id id)) (Fin.natAdd Lyt.ng i):ℝ) < _;rw [degree_right,append_degree]; have hi := inj_degree id Function.injective_id i
                 apply lt_of_lt_of_le _ (le_max_left ..);exact_mod_cast (by omega : degreeOf id i+degreeOf id i < 8)
  · intro i;change degreeOf (Fin.addCases Lyt.bit (Fin.addCases l r)) i ≤ _;rw [append_degree,append_degree];have := h.2 i; have := hl i;have := hr i;omega
private theorem add_sh (n : ℕ) : Sh (AddLayout.layout n) d 2 := by
  refine ⟨fun i => ?_,fun i => (w3_bitDegree _ _).symm.le.trans (AddLayout.bitDegree i)⟩
  apply lt_of_lt_of_le _ (le_max_left ..);exact_mod_cast lt_of_le_of_lt ((w3_gateDegree _ _).symm.le.trans (AddLayout.gateDegree i)) (by decide : 5<8)
private theorem mul_sh : Sh (w3_fpMulLayout d hd) d 2 := by
  refine ⟨fun i => ?_,fun i => ((w3_bitDegree _ _).symm.trans ((w3_fpMulIncidenceBounds hd).2.1 i)).le⟩
  have H := (w3_fpMulIncidenceBounds hd).2.2 i;rw [w3_gateDegree] at H;exact H.trans_le (le_max_right ..)
private theorem anchors_sh (n : ℕ) : Sh (S8H0.AnchoredLayout.anchors n) d 2 := by
  have h := inj_degree (id : Fin n → Fin n) Function.injective_id
  exact ⟨fun i => (Nat.cast_le.mpr (h i)).trans_lt ((by norm_num : ((1:ℕ):ℝ)<8).trans_le (le_max_left ..)),fun i => (h i).trans (by decide)⟩
private theorem reg_inj {n : ℕ} (l : Fin 4) : Function.Injective (fun i : Fin n => AddLayout.reg i l) := by intro x y e;apply Fin.ext;have H := congrArg Fin.val e; simp only [AddLayout.reg] at H;omega
private theorem addr_inj (l : Fin 4) : Function.Injective (fun i => addr hd i l) := (Fin.natAdd_injective ..).comp (reg_inj l)
private theorem out_inj : Function.Injective (@outPos d) := by intro x y e;apply Fin.ext;have H := congrArg Fin.val e; simp only [outPos] at H;omega
private theorem in_inj (b : Bool) : Function.Injective (inPos (d:=d) b) := by intro x y e;apply Fin.ext;have H := congrArg Fin.val e; cases b <;> simp [inPos] at H <;> omega
private theorem mul1_inj : Function.Injective (mul1 hd) := (Fin.castAdd_injective ..).comp ((Fin.castAdd_injective ..).comp (parsimonious hd).1)
private theorem mul2_inj : Function.Injective (mul2 hd) := (Fin.castAdd_injective ..).comp ((Fin.natAdd_injective ..).comp (parsimonious hd).1)

private theorem splitdeg {n m z : ℕ} (a : Fin (n+m) → Fin z) (v) : degreeOf a v = degreeOf (fun i => a (Fin.castAdd m i)) v + degreeOf (fun i => a (Fin.natAdd n i)) v := by
  have e : a=Fin.addCases (fun i => a (Fin.castAdd m i)) (fun i => a (Fin.natAdd n i)) := by funext i;induction i using Fin.addCases <;> simp
  conv_lhs => rw [e]; exact append_degree ..
private theorem linked_sh : Sh (Stage.Links.layout hd) d 6 := by
  apply link_sh (L:=2) (R:=2) (join_shape (join_shape (mul_sh hd) (mul_sh hd)) (add_sh _))
  · intro i; unfold left; rw [append_degree]; exact Nat.add_le_add (inj_degree _ (addr_inj hd 0) _) (inj_degree _ (addr_inj hd 2) _)
  · intro i; unfold right; rw [append_degree]; exact Nat.add_le_add (inj_degree _ ((mul2_inj hd).comp out_inj) _) (inj_degree _ ((mul1_inj hd).comp out_inj) _)
private theorem port_inj (j : Fin 8) (l : Fin 4) : Function.Injective (port (d:=d) hd j l) := by
  intro x y e;exact congrArg Prod.snd (finProdFinEquiv.injective (reg_inj l (Fin.natAdd_injective _ _ e)))
private theorem outaddr_inj : Function.Injective (fun i : Fin d => addr hd ⟨i.val,by clear * - i;omega⟩ 1) := fun x y e => Fin.ext (congrArg (Fin.val (n:=2*d)) (addr_inj hd 1 e))
private theorem a_ties (v : Fin (S8G.FpPhysicalAtom.base d hd).nb) (side : Bool) : degreeOf (fun j => if side then (S8G.FpPhysicalAtom.ties hd j).1 else (S8G.FpPhysicalAtom.ties hd j).2) v ≤ 8 := by
  rw [splitdeg]; apply Nat.add_le_add (rect _ ?_ _) (rect _ ?_ _)
  · intro i;fin_cases i <;> cases side <;> simp only [S8G.FpPhysicalAtom.ties,Fin.addCases_left,Equiv.symm_apply_apply,Bool.false_eq_true,if_false,if_true] <;>
      first | exact (port_inj hd _ _).comp (Fin.castSucc_injective _) | exact (Fin.castAdd_injective ..).comp ((mul1_inj hd).comp (in_inj _)) | exact (Fin.castAdd_injective ..).comp (outaddr_inj hd)
  · intro i;fin_cases i <;> cases side <;> simp only [S8G.FpPhysicalAtom.ties,Fin.addCases_right,Equiv.symm_apply_apply,Bool.false_eq_true,if_false,if_true] <;> exact port_inj hd _ _
private theorem atom_sh : Sh (S8G.FpPhysicalAtom.layout d hd) d 22 := by
  apply link_sh (L:=8) (R:=8) (join_shape (linked_sh hd) (widen (add_sh _) (by decide : 2 ≤ 6))) (fun i => a_ties hd i true) (fun i => a_ties hd i false)
private theorem slot_sh : Sh (slotLayout d k hd) d 24 := by
  apply link_sh (L:=1) (R:=1) (join_shape (atom_sh hd) (widen (anchors_sh _) (by decide : 2 ≤ 22)))
  · apply inj_degree;intro x y e; apply Fin.ext;exact congrArg (Fin.val (n:=d+1)) (port_inj hd 3 0 (Fin.castAdd_injective _ _ e))
  · apply inj_degree;intro x y e;apply Fin.ext;exact congrArg (Fin.val (n:=k)) (Fin.natAdd_injective _ _ e)
private theorem so_inj : Function.Injective (stageOut hd) := (Fin.natAdd_injective ..).comp ((reg_inj 0).comp (Fin.castSucc_injective _))
private theorem op_inj (b : Bool) : Function.Injective (operand hd b) := (Fin.castAdd_injective ..).comp ((mul1_inj hd).comp (in_inj b))
private theorem stage_sh : Sh (boundedStage hd) d 8 := by
  apply link_sh (L:=1) (R:=1) (join_shape (linked_sh hd) (widen (add_sh _) (by decide : 2 ≤ 6))) (inj_degree _ (so_inj hd)) (inj_degree _ ((Fin.castAdd_injective ..).comp (outaddr_inj hd)))
private theorem base_sh : Sh (FpArithNet.base hd m k) d 24 := join_shape (tiled (slot_sh hd) _) (join_shape (tiled (widen (stage_sh hd) (by decide : 8 ≤ 24)) _) (tiled (widen (stage_sh hd) (by decide : 8 ≤ 24)) _))

attribute [-simp] Fin.natAdd_eq_addNat
private theorem slotPort_inj (s : Fin (4*m)) : Function.Injective (slotPort (k:=k) hd s) := by
  intro x y e;exact congrArg Prod.snd (finProdFinEquiv.injective (Fin.castAdd_injective _ _ e))
private theorem stagePort_inj (s : Bool) (n : Fin (2*m)) : Function.Injective (stagePort (k:=k) hd s n) := by
  intro x y e; have h := Fin.natAdd_injective _ _ e; cases s
  · exact congrArg Prod.snd (finProdFinEquiv.injective (Fin.castAdd_injective _ _ h))
  · exact congrArg Prod.snd (finProdFinEquiv.injective (Fin.natAdd_injective _ _ h))
private theorem x_inj : Function.Injective (xBits (k:=k) hd) := (Fin.castAdd_injective ..).comp ((port_inj hd 1 2).comp (Fin.castSucc_injective _))
private theorem factor_deg (v : Fin (FpArithNet.base hd m k).nb) (b : Bool) : degreeOf (fun i => if b then (factorTie hd i).1 else (factorTie hd i).2) v ≤ 4*m := by
  apply rect; intro s;cases b <;> simp only [factorTie,Equiv.symm_apply_apply,Bool.false_eq_true,if_true,if_false]
  · exact (stagePort_inj hd _ _).comp (op_inj hd true)
  · exact (slotPort_inj hd _).comp (x_inj hd)
private theorem chain_deg (v : Fin (FpArithNet.base hd m k).nb) (b : Bool) : degreeOf (fun i => if b then (chainTie hd i).1 else (chainTie hd i).2) v ≤ 4*m := by
  apply rect; intro s;by_cases H : (whichStep s).val=0 <;> cases b <;> simp only [chainTie,Equiv.symm_apply_apply,H,if_true,if_false,Bool.false_eq_true] <;>
    intro x y eq <;> first | exact so_inj hd (stagePort_inj (k:=k) hd _ _ eq) | exact op_inj hd false (stagePort_inj (k:=k) hd _ _ eq)
private theorem ties_deg (v : Fin (FpArithNet.base hd m k).nb) (b : Bool) : degreeOf (fun i => if b then (FpArithNet.ties hd i).1 else (FpArithNet.ties hd i).2) v ≤ 4*m+4*m := by
  rw [splitdeg]; simp only [FpArithNet.ties,Fin.addCases_left,Fin.addCases_right];exact Nat.add_le_add (factor_deg hd v b) (chain_deg hd v b)
private theorem chain_sh : Sh (chains hd m k) d (24+(4*m+4*m)+(4*m+4*m)) :=
  link_sh (base_sh hd) (fun i => ties_deg hd i true) (fun i => ties_deg hd i false)
private theorem pin_l {pre : List Bool} (v : Fin (pinBase hd m k pre).nb) : degreeOf (lhs hd pre) v ≤ 4*m := by
  apply bucket _ (fun u => (finProdFinEquiv.symm (Fin.castLE (min_le_right ..) u : Fin (4*m*d))).1)
  intro a b e h; have eq := Fin.castAdd_injective _ _ h
  let cast (i : Fin (N m d pre)) := (Fin.castLE (min_le_right ..) i : Fin (4*m*d))
  have pp : prefixPort (k:=k) hd (cast a)=prefixPort hd (cast b) := eq
  have aux (x y : Fin (4*m*d)) (he : (finProdFinEquiv.symm x).1=(finProdFinEquiv.symm y).1) (hp : prefixPort (k:=k) hd x=prefixPort hd y) : x=y := by
    obtain ⟨⟨s,j⟩,rfl⟩ := finProdFinEquiv.surjective x; obtain ⟨⟨t,u⟩,rfl⟩ := finProdFinEquiv.surjective y
    simp only [Equiv.symm_apply_apply] at he;subst t; simp only [prefixPort,Equiv.symm_apply_apply] at hp
    rw [x_inj hd (slotPort_inj hd _ hp)]
  exact Fin.ext (congrArg (Fin.val (n:=4*m*d)) (aux _ _ e pp))
private theorem arith_sh : Sh (arith hd m k pre) d (24+(4*m+4*m)+(4*m+4*m)+4*m+1) := by
  apply link_sh (join_shape (chain_sh hd) (widen (anchors_sh _) (by omega))) (pin_l hd)
  apply inj_degree;intro a b e;exact Fin.castSucc_injective _ (Fin.natAdd_injective _ _ e)

theorem uniform_degree (hd2 : 2 ≤ d) (hm' : m=blockCount d) (v : Fin (G).nV) (hv : v ∉ w3_incLookups (layout hd m k pre) sl) :
    (G).deg v ≤ 1000000 * Nat.ceil ((d:ℝ)^((3:ℝ)/4)) := by
  let c := Nat.ceil ((d:ℝ)^((3:ℝ)/4))
  have hc : 1 ≤ c := ceil_pos d hd
  have hr : (d:ℝ)^((3:ℝ)/4) ≤ c := Nat.le_ceil _
  have hm0 := count_sq d hd2; rw [← hm'] at hm0
  have hms : (m:ℝ) ≤ 4*Real.sqrt d := by nlinarith [Real.sq_sqrt (Nat.cast_nonneg d),Real.sqrt_nonneg (d:ℝ),(show (m:ℝ)*m ≤ 16*d by exact_mod_cast hm0)]
  have hbase : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hs := Real.rpow_le_rpow_of_exponent_le hbase (by norm_num : (1:ℝ)/2 ≤ 3/4)
  rw [← Real.sqrt_eq_rpow] at hs; have hmcap : m ≤ 4*c := by exact_mod_cast (show (m:ℝ) ≤ 4*(c:ℝ) by linarith)
  have hpow : ((d:ℝ)+1)^((3:ℝ)/4) ≤ 2*(d:ℝ)^((3:ℝ)/4) := by
    calc _ ≤ (2*(d:ℝ))^((3:ℝ)/4) := Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
         _ = (2:ℝ)^((3:ℝ)/4)*(d:ℝ)^((3:ℝ)/4) := Real.mul_rpow (by norm_num) (by positivity)
         _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)) (by positivity)
  have cap : HashGateLayout.degreeCap d ≤ (300*c:ℕ) := by unfold HashGateLayout.degreeCap;push_cast;apply max_le <;> linarith [show (1:ℝ) ≤ c by exact_mod_cast hc]
  have bound (u : Fin (w3_factorGraph A).nV) : (w3_factorGraph A).deg u ≤ 300*c := by
    induction u using Fin.addCases with
    | left g => rw [w3_gateDegree]; exact_mod_cast ((arith_sh (k:=k) (m:=m) pre hd).1 g).le.trans cap
    | right i => rw [w3_bitDegree];have H := (arith_sh (k:=k) (m:=m) pre hd).2 i;change degreeOf (A).bit i ≤ _;omega
  exact (core_degree F seed P pre nz y input hd bound v hv).trans (by change 300*c+1 ≤ 1000000*c;omega)

/-- A query-independent incidence core with exactly the native input descriptor. -/
theorem query_core (q : w3_Query) (hq : w3_fpQueries q) (mul : w3_modMulInterface) :
    Nonempty {W : w3_WireCore q 1000000 // W.desc = q.input} := by
  have shape := query_shape q hq
  obtain ⟨p,prime,h67,nz,h64,h4096,seed,F,hF,P,y,pre,rfl⟩ := hq
  let d := bitLen p; let m := blockCount d; let T := hashThreshold p (p-1) m (p-1); let k := Nat.clog 2 (2*T)
  have hf := w3_fpPrimeFits prime.out (by omega : 2<p)
  have hd : 2 ≤ d := by by_contra! h; have he := Nat.pow_le_pow_right (by decide : 0<2) (show bitLen p ≤ 1 from (by change d ≤ 1;omega)); norm_num at he; omega
  have hm : 1 ≤ m := (by decide : 1 ≤ 2).trans (le_max_left ..)
  have hp' : 0 < ((p-1:ℕ):ℝ) := by exact_mod_cast nz
  have hq' : 0 < qStar m (p-1) := lt_of_lt_of_le (by positivity : 0 < 4096*m) (le_max_left ..)
  have hT : 0 < T := Nat.ceil_pos.mpr (div_pos (mul_pos (by exact_mod_cast (by omega : 0<p)) (by exact_mod_cast hq')) hp')
  have hk : 1 ≤ k := Nat.clog_pos (by decide) (by omega)
  have fit : T ≤ 2^k := (by omega : T ≤ 2*T).trans (Nat.le_pow_clog (by decide) _)
  let input := OAI.Algorithms.SubexponentialSAT.Encoding.encodeList id [encodeNatListBin [p,(P : ZMod p).val,p-1,T],encodeNatListBin ((List.finRange m).flatMap fun i => [(seed i).1.val+1,(seed i).2.val]),encodeFpFactorBlocks F,encodeNatListBin (List.ofFn fun j => (y j).val),pre]
  let q := native F seed P pre (⟨Nat.ne_of_gt nz⟩ : NeZero (p-1)) y input d k
  change Nonempty {W : w3_WireCore q 1000000 // W.desc=q.input}
  refine ⟨core F seed P pre _ y input hf.1 (by omega) hf.2 fit hm hF mul ?_ ?_ ?_⟩
  · exact shape
  · intro v _; exact uniform_degree F seed P pre _ y input hf.1 hd rfl v ‹_›
  · have h := ceil_pos d hf.1;change 2 ≤ 1000000*Nat.ceil ((d:ℝ)^((3:ℝ)/4));omega


theorem native_core_family : CoreFamily := by
  refine ⟨query_core,?_⟩
  intro p m d k T M prime F seed P pre nz y input hd hd2 hm hp hf hT hm1 hF mul hq
  let sh := query_shape _ hq
  let deg := uniform_degree (k:=k) F seed P pre nz y input hd hd2 hm
  have eqdeg : 2 ≤ 1000000*Nat.ceil ((d:ℝ)^((3:ℝ)/4)) := by have := ceil_pos d hd;omega
  refine ⟨(core F seed P pre nz y input hd hp hf hT hm1 hF mul sh deg eqdeg).1,rfl,rfl,rfl,HEq.rfl,HEq.rfl⟩

attribute [simp] Fin.natAdd_eq_addNat
end DetDLP.M3A.FpWireCore

abbrev solution := @DetDLP.M3A.FpWireCore.native_core_family
