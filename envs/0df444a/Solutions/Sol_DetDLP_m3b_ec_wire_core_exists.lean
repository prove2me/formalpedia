-- Prove2me | solution 1 for DetDLP.m3b_ec_wire_core_exists
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T21:32:16.214604+00:00
-- url     : https://prove2.me/submissions/7716481d-b4dd-439f-8760-83b7d26d9d47

import Theorems.Thm_DetDLP_m3b_ec_body_degree
import Theorems.Thm_DetDLP_m3b_ec_layout_size
import Theorems.Thm_DetDLP_m3b_ec_query_shape
import Theorems.Thm_DetDLP_m3b_ec_precision
import Definitions.Def_DetDLP_M3B_ECNetBijection
import Definitions.Def_DetDLP_S8H0_GraphDegree
import Theorems.Thm_DetDLP_w3_native_lookup_address
import Definitions.Def_DetDLP_S8E_ECTrace

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace DetDLP.M3B.CoreWitness
open S8J S8J.CircuitRealizes S8H0 RegisterMap NamedBlocks
open ECCert ECPhysicalNet
section
variable {m : ℕ}
/-- Slot order in the physical layout alternates sides within each factor pair. -/
def slotNumber : (Fin m × Fin 2 × Bool) ≃ Fin (4*m) where
  toFun t := ix t.2.2 (pointIdx t.1 t.2.1)
  invFun i := (⟨i.val/4,by omega⟩, ⟨i.val/2%2,by omega⟩, decide (i.val%2=1))
  left_inv := by
    rintro ⟨b,j,s⟩; cases s <;> apply Prod.ext <;> first | apply Prod.ext | skip
    all_goals first | apply Fin.ext | skip
    all_goals simp [ix,pointIdx] <;> omega
  right_inv i := Fin.ext (by
    change 2*(2*(i.val/4)+(i.val/2%2)) + (decide (i.val%2=1)).toNat = i.val
    by_cases h : i.val%2=1 <;> simp [h] <;> omega)
end
variable {p m k : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
variable (seed : ECSeed p m) (T : ℕ) (P : Point E) (pre : List Bool)
noncomputable abbrev ar := AnchoredLayout.block (body (k:=k) E seed T P pre).core ((ShapeOf p m k).size+1)
noncomputable abbrev wiring := AnchoredLayout.wiring (body (k:=k) E seed T P pre).core (body (k:=k) E seed T P pre).name
noncomputable abbrev inner := circuit (ar (k:=k) E seed T P pre) (wiring E seed T P pre)
noncomputable abbrev bus (i : Fin (4*m)) (j : Fin k) : Fin (inner (k:=k) E seed T P pre).nb :=
  (wiring E seed T P pre).rep (busAddr i 1 (Fin.castLE (le_max_right _ _) j)).index.castSucc
noncomputable abbrev vertex := ECLayout.vertex (inner (k:=k) E seed T P pre) (bus E seed T P pre)
noncomputable abbrev port := ECLayout.port (inner (k:=k) E seed T P pre) (bus E seed T P pre)
noncomputable def readAddress (i : Fin (4*m))
    (values : Fin ((w3_factorGraph (layout (k:=k) E seed T P pre)).deg (vertex E seed T P pre i)) → Bool) :=
  bitsToNat (fun j : Fin k => values (port E seed T P pre i j))

variable (F : Fin m → List (Point E)) (hT : T ≤ p) (hk : 2*T ≤ 2^k) (hF : ListsOK E F seed T) (hp : 3 < p) (hm : 1 ≤ m)
/-- Read the significance-ordered address bits at the actual lookup vertex.
    The edge assignment, not a named-register environment, supplies these bits. -/
theorem local_address (a : {x // (w3_factorGraph (layout (k:=k) E seed T P pre)).Satisfies (w3_factorChecks _ (test E seed T P pre)) x})
    (b : Fin m) (j : Fin 2) (s : Bool) :
    let i := ix s (pointIdx b j)
    let x := w3_factorEquiv _ _ a
    let t := (ECNetBijection.acceptEquiv E seed T P pre F hT hk hF hp hm x).val
    readAddress E seed T P pre i (w3_wireLocal _ (vertex E seed T P pre i) a.val) =
      ECAddress.address E seed T b ((F b).get (if s then t.2 b j else t.1 b j)) := by
  apply Eq.trans _ (physical_address E seed T P pre F hT hk hF (w3_factorEquiv _ _ a) b j s)
  apply congrArg bitsToNat; funext l
  exact ECLayout.read_accepted (inner (k:=k) E seed T P pre) (bus E seed T P pre)
    (CircuitRealizes.test (ar E seed T P pre) (wiring E seed T P pre)) a _ l


private theorem vertex_inj : Function.Injective (vertex (k:=k) E seed T P pre) := by
  intro i j he
  have h := congrArg Fin.val he
  change (inner (k:=k) E seed T P pre).ng + i.val = (inner (k:=k) E seed T P pre).ng + j.val at h
  exact Fin.ext (Nat.add_left_cancel h)

noncomputable def address (v : Fin (w3_factorGraph (layout (k:=k) E seed T P pre)).nV)
    (values : Fin ((w3_factorGraph (layout (k:=k) E seed T P pre)).deg v) → Bool) : ℕ := by
  classical
  exact if h : ∃ i, vertex E seed T P pre i = v then
    readAddress E seed T P pre h.choose (h.choose_spec.symm ▸ values) else 0

theorem address_vertex (i : Fin (4*m)) (values : Fin ((w3_factorGraph (layout (k:=k) E seed T P pre)).deg (vertex E seed T P pre i)) → Bool) :
    address E seed T P pre _ values = readAddress E seed T P pre i values := by
  classical
  have h : ∃ j, vertex (k:=k) E seed T P pre j = vertex E seed T P pre i := ⟨i,rfl⟩
  unfold address; rw [dif_pos h]
  have eq := vertex_inj E seed T P pre h.choose_spec
  have aux (j : Fin (4*m)) (e : vertex (k:=k) E seed T P pre j = vertex E seed T P pre i) (hji : j = i) :
      readAddress E seed T P pre j (e.symm ▸ values) = readAddress E seed T P pre i values := by subst j; rfl
  exact aux _ h.choose_spec eq

section Query
variable {M : ℕ} [NeZero M] (y : w3_Label M (base E F).totalCoords) (input : List Bool)
noncomputable def query : w3_Query where
  V := Point E
  M := M
  nz := inferInstance
  b := bitLen p
  m := m
  k := k
  FB := base E F
  P := P
  y := y
  code := w3_tupleWord (base E F) (fun A => (pointCoords A).flatMap (w3_bits (bitLen p)))
  pre := pre
  input := input
  addr i j := ECAddress.address E seed T i ((F i).get j)

noncomputable abbrev slots := ECLayout.gateSlots (q:=query (k:=k) E seed T P pre F y input) (inner (k:=k) E seed T P pre) (bus E seed T P pre) slotNumber.symm
private theorem gate_at (u : Fin m × Fin 2 × Bool) :
    (slots (k:=k) E seed T P pre F y input).symm (.inl u) = Fin.natAdd (inner (k:=k) E seed T P pre).ng (slotNumber u) := by
  change finSumFinEquiv (.inr (slotNumber u)) = _
  exact finSumFinEquiv_apply_right ..
private theorem inc_at (u : Fin m × Fin 2 × Bool) :
    (w3_incSlot (layout (k:=k) E seed T P pre) (slots E seed T P pre F y input)).symm (.inl u) = vertex E seed T P pre (slotNumber u) := by
  change finSumFinEquiv (.inl ((slots E seed T P pre F y input).symm (.inl u))) = _
  rw [finSumFinEquiv_apply_left, gate_at]; rfl

theorem lookupDegree (u : Fin m × Fin 2 × Bool) :
    (w3_factorGraph (layout (k:=k) E seed T P pre)).deg (Fin.castAdd _ ((slots E seed T P pre F y input).symm (.inl u))) = k := by
  rw [gate_at]; exact ECLayout.lookup_degree (inner E seed T P pre) (bus E seed T P pre) _

theorem lookupAddress (a : {x // (w3_factorGraph (layout (k:=k) E seed T P pre)).Satisfies (w3_factorChecks _ (test E seed T P pre)) x})
    (b : Fin m) (j : Fin 2) (s : Bool) :
    let q := query (k:=k) E seed T P pre F y input
    let t := (ECNetBijection.acceptEquiv E seed T P pre F hT hk hF hp hm (w3_factorEquiv _ _ a)).val
    let v := (w3_incSlot (layout (k:=k) E seed T P pre) (slots E seed T P pre F y input)).symm (.inl (b,j,s))
    address E seed T P pre v (w3_wireLocal _ v a.val) = q.addr b (if s then t.2 b j else t.1 b j) := by
  let G := w3_factorGraph (layout (k:=k) E seed T P pre)
  let read := fun v : Fin G.nV => address E seed T P pre v (w3_wireLocal G v a.val)
  exact (congrArg read (inc_at (k:=k) E seed T P pre F y input (b,j,s))).trans
    ((address_vertex E seed T P pre _ _).trans (local_address E seed T P pre F hT hk hF hp hm a b j s))
/-- Incidence core with all assignment, lookup-count, port-degree, and address
    obligations discharged. Only external resource bounds and injectivity remain. -/
noncomputable def coreOfBounds {C S : ℕ} (hp : 3 < p) (hm : 1 ≤ m)
    (hi : ∀ i, Function.Injective ((query (k:=k) E seed T P pre F y input).addr i))
    (he : 2*(layout (k:=k) E seed T P pre).ne ≤ S)
    (hd : ∀ v ∉ w3_incLookups (layout (k:=k) E seed T P pre) (slots E seed T P pre F y input),
      (w3_factorGraph (layout (k:=k) E seed T P pre)).deg v ≤ C * Nat.ceil (((bitLen p : ℕ):ℝ)^((3:ℝ)/4)))
    (heq : 2 ≤ C * Nat.ceil (((bitLen p : ℕ):ℝ)^((3:ℝ)/4)))
    (shape : let q := query (k:=k) E seed T P pre F y input
      2 ≤ q.b ∧ 1 ≤ q.m ∧ 1 ≤ q.k ∧ blockCount q.b ≤ C*q.m ∧ q.m ≤ C*blockCount q.b ∧
      S ≤ C*q.m*q.b ∧ 4*q.m*q.k ≤ C*q.b ∧ q.b ≤ C*(4*q.m*q.k) ∧
      1 ≤ w3_precision q ∧ w3_precision q ≤ S ∧ 1 ≤ w3_len q ∧ w3_len q ≤ C*q.m) :
    w3_WireCore (query (k:=k) E seed T P pre F y input) C :=
  w3_incCore (layout E seed T P pre) (slots E seed T P pre F y input) (test E seed T P pre)
    (ECNetBijection.acceptEquiv E seed T P pre F hT hk hF hp hm) (address E seed T P pre) hi
    (lookupAddress E seed T P pre F hT hk hF hp hm y input) (lookupDegree E seed T P pre F y input) he hd heq shape
end Query

end DetDLP.M3B.CoreWitness

open DetDLP DetDLP.M3B S8H0 ECPhysicalNet ECCert CoreWitness
open OAI.Algorithms.SubexponentialSAT

namespace LocalDegree
open DetDLP DetDLP.S8H0 DetDLP.M3B S8J S8H S8J.CircuitRealizes RegisterMap NamedBlocks GraphDegree ECPhysicalNet ECCert
section
variable {p m k : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (seed : ECSeed p m) (T : ℕ) (P : Point E) (pre : List Bool)
private noncomputable abbrev ar := AnchoredLayout.block (body (k:=k) E seed T P pre).core ((ShapeOf p m k).size+1)
private noncomputable abbrev wiring := AnchoredLayout.wiring (body (k:=k) E seed T P pre).core (body (k:=k) E seed T P pre).name
private noncomputable abbrev inner := circuit (ar (k:=k) E seed T P pre) (wiring E seed T P pre)
private noncomputable abbrev bus (i : Fin (4*m)) (j : Fin k) : Fin (inner (k:=k) E seed T P pre).nb :=
  (wiring E seed T P pre).rep (busAddr i 1 (Fin.castLE (le_max_right _ _) j)).index.castSucc
end

private theorem ranges (n m : ℕ) : List.finRange (n+m) =
    (List.finRange n).map (Fin.castAdd m) ++ (List.finRange m).map (Fin.natAdd n) := by
  apply List.ext_getElem <;> simp
  case h =>
    intro i hi; by_cases h : i < n
    · rw [List.getElem_append_left (by simpa using h)]; simp
    · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt h)]; apply Fin.ext; simp; omega

private theorem appendedBit (A : w3_FactorLayout) {n k : ℕ} (u : Fin n → Fin k → Fin A.nb)
    (h : Function.Injective (fun e : Fin (n*k) => u (ECLayout.row e) (ECLayout.column e))) (b : Fin A.nb) :
    (w3_factorGraph (ECLayout.layout A u)).deg (Fin.natAdd _ b) ≤ (w3_factorGraph A).deg (Fin.natAdd _ b)+1 := by
  let f := fun e : Fin (n*k) => u (ECLayout.row e) (ECLayout.column e)
  let l := (List.finRange (n*k)).filter (fun e => decide (f e = b))
  have nd : l.Nodup := (List.nodup_finRange _).filter _
  have ss : Subsingleton ↥l.toFinset := ⟨fun a c => Subtype.ext (h (((show f a.val = b by simpa [l] using a.property)).trans (show f c.val = b by simpa [l] using c.property).symm))⟩
  have one : l.length ≤ 1 := by
    have hcard := Fintype.card_le_one_iff_subsingleton.mpr ss
    rw [Fintype.card_coe,List.toFinset_card_of_nodup nd] at hcard; exact hcard
  rw [w3_bitDegree (ECLayout.layout A u) b,w3_bitDegree A b]; change degreeOf (Fin.addCases A.bit f) b ≤ degreeOf A.bit b + 1
  simp only [degreeOf,ranges A.ne (n*k),List.filter_append,List.filter_map,Function.comp_def,Fin.addCases_left,Fin.addCases_right,List.length_append,List.length_map]; exact Nat.add_le_add_left one _

private theorem lowInj {p m k : ℕ} {E : WeierstrassCurve (ZMod p)} [Fact p.Prime] [E.IsElliptic] (seed : ECSeed p m) (T : ℕ) (P : Point E) (pre : List Bool) :
    Function.Injective (fun e : Fin (4*m*k) => bus E seed T P pre (ECLayout.row e) (ECLayout.column e)) := by
  intro a b he
  have hr := Fin.castAdd_injective _ _ he
  have hi := Fin.castSucc_injective _ hr
  have hp := Fin.castAdd_injective _ _ hi
  have pair := finProdFinEquiv.injective hp
  have hrow := congrArg Prod.fst pair
  apply finProdFinEquiv.symm.injective; apply Prod.ext
  · exact hrow
  have hj := congrArg Prod.snd pair
  have hh := Fin.natAdd_injective _ _ hj
  have hh := Fin.natAdd_injective _ _ hh
  have hh := Fin.natAdd_injective _ _ hh
  have hp2 := finProdFinEquiv.injective hh
  exact Fin.ext (congrArg (fun x => x.2.val) hp2)

theorem bounded_nonlookup {p m k : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (seed : ECSeed p m) (T : ℕ) (P : Point E) (pre : List Bool) (hbody : good (body (k:=k) E seed T P pre) (cap p))
    (v : Fin (w3_factorGraph (layout (k:=k) E seed T P pre)).nV) (hv : v.val + 4*m < (layout (k:=k) E seed T P pre).ng ∨ (layout (k:=k) E seed T P pre).ng ≤ v.val) :
    (w3_factorGraph (layout (k:=k) E seed T P pre)).deg v ≤ cap p := by
  let b := (body (k:=k) E seed T P pre).core
  let f := (body (k:=k) E seed T P pre).name
  let K := (ShapeOf p m k).size+1
  let A := inner (k:=k) E seed T P pre
  let u := bus (k:=k) E seed T P pre
  induction v using Fin.addCases with
  | left g =>
    induction g using Fin.addCases with
    | left g =>
      apply (ECLayout.ordinary_degree A u g).le.trans
      induction g using Fin.addCases with
      | left g =>
        apply (NamedWires.oldDegree (AnchoredLayout.signal b f) (AnchoredLayout.block b K).A.gate g).le.trans
        induction g using Fin.addCases with
        | left i => exact (degree_left (AnchoredLayout.anchors K).gate b.A.gate i).le.trans (anchors_ok K _ (small p 1 (by decide)) i)
        | right i => exact (degree_right (AnchoredLayout.anchors K).gate b.A.gate i).le.trans (hbody i)
      | right i => exact (NamedWires.eqDegree (AnchoredLayout.signal b f) (AnchoredLayout.block b K).A.gate i).le.trans (small p _ (by decide))
    | right i =>
      change ((A.ng + i.val) + 4*m < A.ng + 4*m ∨ A.ng + 4*m ≤ A.ng + i.val) at hv
      have := i.isLt; omega
  | right i =>
    apply (appendedBit A u (lowInj seed T P pre) i).trans
    change (w3_factorGraph (CopyCycle.layout _ _)).deg (Fin.natAdd _ i)+1 ≤ _
    exact (Nat.add_le_add_right (CopyCycle.bitDegree (ar (k:=k) E seed T P pre).A.gate (wiring E seed T P pre).next i).le 1).trans (small p 4 (by decide))
end LocalDegree

private theorem cap_bound (p : ℕ) (hb : 2 ≤ bitLen p) : GraphDegree.cap p ≤ 100000000*⌈((bitLen p:ℝ)^((3:ℝ)/4))⌉₊ := by
  let b : ℝ := bitLen p
  have b2 : 2 ≤ b := by dsimp [b]; exact_mod_cast hb
  have b0 : 0 ≤ b := by linarith
  have e0 : 0 ≤ b^((3:ℝ)/4) := Real.rpow_nonneg b0 _
  have e1 : 1 ≤ b^((3:ℝ)/4) := Real.one_le_rpow (by linarith) (by norm_num)
  have hh := Nat.le_ceil (b^((3:ℝ)/4))
  have c1 : 1 ≤ ⌈b^((3:ℝ)/4)⌉₊ := by exact_mod_cast e1.trans hh
  apply max_le (by change 12 ≤ 100000000*⌈b^((3:ℝ)/4)⌉₊; omega)
  apply Nat.ceil_le.mpr
  have h := Real.rpow_le_rpow (by linarith : 0 ≤ b+2) (by linarith : b+2 ≤ 2*b) (by norm_num : (0:ℝ) ≤ 3/4)
  rw [Real.mul_rpow (by norm_num) b0] at h
  have pow2 : (2:ℝ)^((3:ℝ)/4) ≤ 2 := by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by norm_num : (3:ℝ)/4 ≤ 1)
  change 136*(b+2)^((3:ℝ)/4) ≤ _; push_cast; nlinarith [mul_le_mul_of_nonneg_right pow2 e0]

theorem solution (q : w3_Query) (hq : w3_ecQueries q) : ∃ W : w3_WireCore q 100000000, W.desc = q.input ∧ W.S = 100000000*q.m*q.b := by
  obtain ⟨hu,hl,hk⟩ := m3b_ec_query_shape q hq
  have prec := m3b_ec_precision q hq hu
  have hi := w3_native_lookup_address q (Or.inr hq)
  obtain ⟨p,ip,E,hE,h1,h2,h3,p67,g64,hNZ,hM,seed,F,hF,P,y,pre,rfl⟩ := hq
  letI := ecPointFintype E
  let g := Fintype.card E.toAffine.Point
  let b := bitLen p
  let m := blockCount b
  let T := hashThreshold p (g-1) m g
  let k := Nat.clog 2 (2*T)
  let w := Encoding.encodeList id [encodeCurveInput p E,encodeNatListBin (pointCoords P),encodeNatListBin [g,T],encodeNatListBin ((List.finRange m).flatMap fun i => [(seed i false).1.val+1,(seed i false).2.val,(seed i true).1.val+1,(seed i true).2.val]),encodeECFactorBlocks F,encodeNatListBin (List.ofFn fun j => (y j).val),pre]
  let Q := query (k:=k) E seed T P pre F y w
  have hm : 2 ≤ m := le_max_left ..
  have hbp : p ≤ 2^b := Nat.le_pow_clog (by decide) _
  have hb : 2 ≤ b := by by_contra! h; have := Nat.pow_le_pow_right (by decide : 0<2) (show b ≤ 1 by omega); omega
  have ht : T ≤ p := s8e.threshold_le hm g64 hM
  have hk' : k ≤ b+1 := Nat.clog_le_of_le_pow (by rw [pow_succ]; omega)
  have bb := m3b_ec_body_degree (k:=k) E seed T P pre
  have hd (v : Fin (w3_factorGraph (layout (k:=k) E seed T P pre)).nV) (hv : v ∉ w3_incLookups (layout (k:=k) E seed T P pre) (slots E seed T P pre F y w)) :
      (w3_factorGraph (layout (k:=k) E seed T P pre)).deg v ≤ 100000000*⌈((b:ℝ)^((3:ℝ)/4))⌉₊ := by
    apply (LocalDegree.bounded_nonlookup E seed T P pre bb v ?_).trans (cap_bound p hb)
    let A := CoreWitness.inner (k:=k) E seed T P pre
    by_contra! hn
    change A.ng+4*m ≤ v.val+4*m ∧ v.val < A.ng+4*m at hn
    let j : Fin (4*m) := ⟨v.val-A.ng,by omega⟩
    apply hv; apply Finset.mem_image.mpr
    refine ⟨(slotNumber (m:=m)).symm j,Finset.mem_univ _,?_⟩
    change Fin.castAdd A.nb (finSumFinEquiv (.inr (slotNumber (slotNumber.symm j)))) = v
    rw [Equiv.apply_symm_apply,finSumFinEquiv_apply_right]; apply Fin.ext; change A.ng+(v.val-A.ng)=v.val; omega
  have shape : 2 ≤ Q.b ∧ 1 ≤ Q.m ∧ 1 ≤ Q.k ∧ blockCount Q.b ≤ 100000000*Q.m ∧ Q.m ≤ 100000000*blockCount Q.b ∧ 100000000*m*b ≤ 100000000*Q.m*Q.b ∧ 4*Q.m*Q.k ≤ 100000000*Q.b ∧ Q.b ≤ 100000000*(4*Q.m*Q.k) ∧ 1 ≤ w3_precision Q ∧ w3_precision Q ≤ 100000000*m*b ∧ 1 ≤ w3_len Q ∧ w3_len Q ≤ 100000000*Q.m := by
    change 4*m*k ≤ 2000*b at hu; change b ≤ 4*m*k at hl
    exact ⟨hb,by change 1 ≤ m; omega,hk,by change m ≤ 100000000*m; omega,by change m ≤ 100000000*m; omega,le_rfl,by change 4*m*k ≤ 100000000*b; omega,by change b ≤ 100000000*(4*m*k); omega,by unfold w3_precision; omega,prec,by unfold w3_len; omega,by change 4*(2*m)+2+1 ≤ 100000000*m; omega⟩
  refine ⟨coreOfBounds E seed T P pre F ht (Nat.le_pow_clog (by decide) _) hF y w (by omega) (show 1 ≤ m by omega) (fun j => (hi j).1) (m3b_ec_layout_size E seed T P pre (show 1 ≤ m by omega) (show 1 ≤ b by omega) hk') hd ?_ shape,rfl,rfl⟩
  exact (show 2 ≤ GraphDegree.cap p from GraphDegree.small p 2 (by decide)).trans (cap_bound p hb)

