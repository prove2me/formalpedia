-- Prove2me | solution 1 for DeMorganApprox.Main.lemma_5_9
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:18:47.228468+00:00
-- url     : https://prove2.me/submissions/8ecb9147-e74b-462b-99e7-b2ebf19187d6

import Definitions.Def_DeMorganApprox_Main_HeavyChains

open DeMorganApprox.Main

set_option maxHeartbeats 2500000

namespace ChainEnergy
variable {m : ℕ}

private lemma angle_ok {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ Real.sqrt (a / (a+b)) ∧ 0 ≤ Real.sqrt (b / (a+b)) ∧
    (Real.sqrt (a / (a+b)))^2 + (Real.sqrt (b / (a+b)))^2 ≤ 1 := by
  refine ⟨Real.sqrt_nonneg _,Real.sqrt_nonneg _,?_⟩
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), ←add_div]
  rcases eq_or_ne (a+b) 0 with h|h <;> simp [h]

private lemma params_nonneg (tie : TieRule) (T : Formula m) :
    0 ≤ (chainParams tie T).1 ∧ 0 ≤ (chainParams tie T).2 := by
  have aux {g : Bool} {t : TieRule} {p q : ℝ × ℝ} {φ ψ : Formula m}
      (hp : 0 ≤ p.1 ∧ 0 ≤ p.2) (hq : 0 ≤ q.1 ∧ 0 ≤ q.2) :
      0 ≤ (nodeParams g t φ ψ p q).1 ∧ 0 ≤ (nodeParams g t φ ψ p q).2 := by
    have hs (L : Formula m) (v : ℝ × ℝ) : 0 ≤ helperBoundOf L v := by
      unfold helperBoundOf
      split <;> positivity
    rcases hp with ⟨hp,hp'⟩
    rcases hq with ⟨hq,hq'⟩
    have hsl := hs φ p
    have hsr := hs ψ q
    cases hd : heavyDir t φ ψ <;> cases g <;>
      simp only [nodeParams, hd, gateParams, andParams, orParams, Bool.false_eq_true, if_true, if_false] <;>
      simp only [Bool.not_true, Bool.not_false, pick, if_true, Bool.false_eq_true, if_false] <;> constructor <;> positivity
  induction T generalizing tie with
  | lit => exact ⟨by norm_num [chainParams],by norm_num [chainParams]⟩
  | and p q hp hq => exact aux (hp _) (hq _)
  | or p q hp hq => exact aux (hp _) (hq _)

private def OK (v : ℝ × ℝ) := 0 ≤ v.1 ∧ 0 ≤ v.2 ∧ v.1^2 + v.2^2 ≤ 1

private lemma node_ok (g : Bool) (t : TieRule) (φ ψ : Formula m) :
    OK (nodeAngle g t φ ψ (chainParams (t.sub false) φ) (chainParams (t.sub true) ψ)) := by
  unfold nodeAngle
  dsimp only
  generalize h : heavyDir t φ ψ = d
  have hs (L : Formula m) (v : ℝ × ℝ) : 0 ≤ helperBoundOf L v := by
    unfold helperBoundOf
    split <;> positivity
  have hor {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : OK (orAngle a b) := by
    simpa [OK, orAngle, show a + b + 2 = (a+1)+(b+1) by ring] using
      angle_ok (a := a+1) (b := b+1) (by positivity) (by positivity)
  have hand {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : OK (andAngle a b) := angle_ok ha hb
  cases d <;> cases g <;> simp only [gateAngle, Bool.false_eq_true, if_true, if_false] <;>
    first | exact hand (params_nonneg _ _).2 (hs _ _) | exact hor (params_nonneg _ _).1 (hs _ _)

private lemma conn_ok (a b : ℝ) : OK (connAngle a b) := by
  simpa [OK, connAngle] using angle_ok (a:=1) (b:=Real.sqrt (b/(a+1))) (by norm_num) (Real.sqrt_nonneg _)

@[simp] private lemma unc_coord (d : Bool) (k : Coord) : (k.cons d).uncons = some (d,k) := by cases k <;> rfl
@[simp] private lemma unc_col (d : Bool) (j : Col) : (j.cons d).uncons = some (d,j) := by cases j <;> rfl
@[simp] private lemma coord_cons_ne_top (d : Bool) (k : Coord) : k.cons d ≠ .helper [] := by cases k <;> simp [Coord.cons]
@[simp] private lemma col_cons_ne_rot (d : Bool) (j : Col) : j.cons d ≠ .rot [] := by cases j <;> simp [Col.cons]
@[simp] private lemma col_cons_ne_conn (d : Bool) (j : Col) : j.cons d ≠ .conn [] := by cases j <;> simp [Col.cons]

private lemma dir_sums {α : Type} [DecidableEq α] (push : Bool → α → α)
    (unpush : α → Option (Bool × α)) (inv : ∀ d a, unpush (push d a) = some (d,a))
    (d : Bool) (A B : Finset α) (f : α → ℝ) :
    ∑ a ∈ A.image (push d) ∪ B.image (push (!d)), f a =
      (∑ a ∈ A, f (push d a)) + ∑ a ∈ B, f (push (!d) a) := by
  have hinj (e : Bool) : Function.Injective (push e) := by
    intro a b h
    simpa [inv] using congrArg unpush h
  rw [Finset.sum_union, Finset.sum_image (hinj _).injOn, Finset.sum_image (hinj _).injOn]
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j,_,he⟩ := Finset.mem_image.mp hb
  have := congrArg unpush he
  cases d <;> simp [inv] at this

private def pairRows (d : Bool) (H L : Finset Coord) :=
  insert (Coord.helper []) (H.image (Coord.cons d) ∪ L.image (Coord.cons (!d)))

private lemma pairRows_sum (d : Bool) (H L : Finset Coord) (f : Coord → ℝ) :
    ∑ k ∈ pairRows d H L, f k = f (.helper []) +
      ((∑ k ∈ H, f (k.cons d)) + ∑ k ∈ L, f (k.cons (!d))) := by
  unfold pairRows
  rw [Finset.sum_insert (by simp), dir_sums Coord.cons Coord.uncons unc_coord]

private def rows : Formula m → Finset Coord
  | .lit _ _ => {.leaf []}
  | .and p q | .or p q => pairRows false (rows p) (rows q)

private lemma gateRows (g d : Bool) (p q : Formula m) :
    rows (mkGate g p q) = pairRows d (rows (pick d p q)) (rows (pick (!d) p q)) := by
  cases d <;> cases g <;> simp [rows,mkGate,pick,pairRows,Finset.union_comm]

private lemma root_mem (p : Formula m) : exportKey p ∈ rows p := by
  cases p <;> simp [exportKey, Formula.isLeaf, rows, pairRows]

private noncomputable def pairing (T : Formula m) (x v : Coord → ℝ) :=
  ∑ k ∈ rows T, x k * v k

private noncomputable def mass (T : Formula m) (x : Coord → ℝ) :=
  ∑ k ∈ rows T, (x k)^2

private noncomputable def uval (t : TieRule) (T : Formula m) (x : Coord → ℝ) :=
  pairing T x (chainU t T)

private noncomputable def energy (t : TieRule) (T : Formula m) (x : Coord → ℝ) (J : Finset Col) :=
  ∑ j ∈ J, (pairing T x (fun k => |colVec t T j k|))^2

private lemma basis_pair (T : Formula m) (x : Coord → ℝ) :
    pairing T x (exportV T) = x (exportKey T) := by
  simp [pairing, exportV, basisV, mul_ite, root_mem]

private lemma u_nonneg (t : TieRule) (T : Formula m) (k : Coord) : 0 ≤ chainU t T k := by
  have bas (j k : Coord) : 0 ≤ basisV j k := by simp [basisV]; split <;> norm_num
  have lift {v : Coord → ℝ} (hv : ∀ k, 0 ≤ v k) (d : Bool) (k : Coord) : 0 ≤ liftV d v k := by
    simp only [liftV]; split <;> try positivity
    split <;> first | apply hv | positivity
  have step (t : TieRule) (k : Coord) (g : Bool) (p q : Formula m) (hp : ∀ t k, 0 ≤ chainU t p k) (hq : ∀ t k, 0 ≤ chainU t q k) :
      0 ≤ uStep g t p q (chainU (t.sub false) p) (chainU (t.sub true) q) k := by
    obtain ⟨hc,hs,_⟩ := node_ok g t p q
    simp only [uStep, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    apply add_nonneg (mul_nonneg hc (lift _ _ _)) (mul_nonneg hs (lift (bas _) _ _))
    intro j
    split <;> first | apply hp | apply hq
  induction T generalizing t k with
  | lit i b => exact bas _ _
  | and p q hp hq => exact step t k false p q hp hq
  | or p q hp hq => exact step t k true p q hp hq


private def restrictRow (x : Coord → ℝ) (d : Bool) : Coord → ℝ := fun k => x (k.cons d)

private lemma restrict_eq (x : Coord → ℝ) (d : Bool) : restrictRow x d = fun k => x (k.cons d) := rfl

private lemma pair_gate (g d : Bool) (p q : Formula m) (x v : Coord → ℝ) :
    pairing (mkGate g p q) x v = x (.helper []) * v (.helper []) +
      (pairing (pick d p q) (restrictRow x d) (restrictRow v d) +
       pairing (pick (!d) p q) (restrictRow x (!d)) (restrictRow v (!d))) := by
  unfold pairing
  rw [gateRows g d, pairRows_sum]
  rfl

private lemma mass_gate (g d : Bool) (p q : Formula m) (x : Coord → ℝ) :
    mass (mkGate g p q) x = (x (.helper []))^2 +
      (mass (pick d p q) (restrictRow x d) + mass (pick (!d) p q) (restrictRow x (!d))) := by
  unfold mass
  rw [gateRows g d, pairRows_sum]
  rfl

@[simp] private lemma pairing_zero (T : Formula m) (x : Coord → ℝ) :
    pairing T x (fun _ => 0) = 0 := by simp [pairing]

@[simp] private lemma pairing_smul (T : Formula m) (x v : Coord → ℝ) (a : ℝ) :
    pairing T x (fun k => a * v k) = a * pairing T x v := by
  simp [pairing, Finset.mul_sum, mul_left_comm]

@[simp] private lemma lift_top (d : Bool) (v : Coord → ℝ) : liftV d v (.helper []) = 0 := rfl
@[simp] private lemma lift_cons (d e : Bool) (v : Coord → ℝ) (k : Coord) :
    liftV d v (k.cons e) = if e = d then v k else 0 := by simp [liftV]

private lemma abs_export (T : Formula m) (k : Coord) : |exportV T k| = exportV T k := by
  simp [exportV,basisV]; split <;> norm_num

private lemma pass_col (g d : Bool) (t : TieRule) (p q : Formula m) (j : Col) :
    colVec t (mkGate g p q) (j.cons d) =
      liftV d (colVec (t.sub d) (pick d p q) j) := by
  cases g <;> cases d <;> simp [mkGate,pick,colVec,colStep]

private lemma pair_pass (g d : Bool) (t : TieRule) (p q : Formula m) (j : Col) (x : Coord → ℝ) :
    pairing (mkGate g p q) x (fun k => |colVec t (mkGate g p q) (j.cons d) k|) =
    pairing (pick d p q) (restrictRow x d) (fun k => |colVec (t.sub d) (pick d p q) j k|) := by
  rw [pair_gate g d]
  cases d <;> simp [pass_col, restrict_eq]

private noncomputable abbrev ang (g : Bool) (t : TieRule) (p q : Formula m) :=
  nodeAngle g t p q (chainParams (t.sub false) p) (chainParams (t.sub true) q)

private lemma u_exp (g : Bool) (t : TieRule) (p q : Formula m) :
    let d := heavyDir t p q
    chainU t (mkGate g p q) =
      (ang g t p q).1 • liftV d (chainU (t.sub d) (pick d p q)) +
      (ang g t p q).2 • liftV (!d) (exportV (pick (!d) p q)) := by
  cases hd : heavyDir t p q <;> cases g <;>
    simp [ang,mkGate,chainU,uStep,hd,pick]

private lemma u_at_top (g : Bool) (t : TieRule) (p q : Formula m) :
    chainU t (mkGate g p q) (.helper []) = 0 := by simp [u_exp]

private lemma u_pair (g : Bool) (t : TieRule) (p q : Formula m) (x : Coord → ℝ) :
    let d := heavyDir t p q
    uval t (mkGate g p q) x =
      (ang g t p q).1 * uval (t.sub d) (pick d p q) (restrictRow x d) +
      (ang g t p q).2 * restrictRow x (!d) (exportKey (pick (!d) p q)) := by
  unfold uval
  rw [pair_gate g (heavyDir t p q), u_exp]
  cases hd : heavyDir t p q <;> simp [restrict_eq, basis_pair]

private lemma rot_exp (t : TieRule) (p q : Formula m) :
    let d := heavyDir t p q
    colVec t (mkGate true p q) (.rot []) =
      (ang true t p q).2 • liftV d (chainU (t.sub d) (pick d p q)) -
      (ang true t p q).1 • liftV (!d) (exportV (pick (!d) p q)) := rfl

private lemma rot_pair (t : TieRule) (p q : Formula m) (x : Coord → ℝ) :
    let d := heavyDir t p q
    pairing (mkGate true p q) x (fun k => |colVec t (mkGate true p q) (.rot []) k|) =
      (ang true t p q).2 * uval (t.sub d) (pick d p q) (restrictRow x d) +
      (ang true t p q).1 * restrictRow x (!d) (exportKey (pick (!d) p q)) := by
  obtain ⟨hc,hs,_⟩ := node_ok true t p q
  change 0 ≤ (ang true t p q).1 at hc
  change 0 ≤ (ang true t p q).2 at hs
  rw [pair_gate true (heavyDir t p q), rot_exp]
  cases hd : heavyDir t p q <;> simp [restrict_eq, abs_mul, abs_of_nonneg hc,
    abs_of_nonneg hs, abs_of_nonneg (u_nonneg _ _ _), abs_export, basis_pair, uval]

private lemma conn_pair (g : Bool) (t : TieRule) (p q : Formula m) (x : Coord → ℝ) :
    let T := mkGate g p q
    let a := connAngle (chainParams t T).1 (chainParams t T).2
    pairing T x (fun k => |colVec t T (.conn []) k|) =
      a.1 * x (.helper []) + a.2 * uval t T x := by
  let T := mkGate g p q
  let a := connAngle (chainParams t T).1 (chainParams t T).2
  have hc : 0 ≤ a.1 := (conn_ok _ _).1
  have hs : 0 ≤ a.2 := (conn_ok _ _).2.1
  have he : colVec t T (.conn []) = a.1 • basisV (.helper []) - a.2 • chainU t T := by
    cases g <;> rfl
  have hpt (k : Coord) : |colVec t T (.conn []) k| =
      a.1 * basisV (.helper []) k + a.2 * chainU t T k := by
    rw [he]
    by_cases hk : k = .helper []
    · subst k; simp [T, u_at_top, basisV, abs_of_nonneg hc]
    · simp [basisV,hk,abs_mul,abs_of_nonneg hs,abs_of_nonneg (u_nonneg _ _ _)]
  have hm : Coord.helper [] ∈ rows T := by simp [T,gateRows g false,pairRows]
  change pairing T x (fun k => |colVec t T (.conn []) k|) = a.1 * x (.helper []) + a.2 * uval t T x
  simp only [hpt, pairing, uval, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  simp [basisV,mul_ite, hm, mul_assoc, mul_left_comm, mul_comm]


private lemma gateCols (g : Bool) (t : TieRule) (p q : Formula m) :
    let d := heavyDir t p q
    chainCols t (mkGate g p q) =
      ((chainCols (t.sub d) (pick d p q)).image (Col.cons d) ∪
      (fullCols (t.sub (!d)) (pick (!d) p q)).image (Col.cons (!d))) ∪
      (if g then {.rot []} else ∅) := by
  cases hd : heavyDir t p q <;> cases g <;> simp [mkGate, chainCols,colsStep,hd,pick,fullCols]

private lemma gateCoords (g : Bool) (t : TieRule) (p q : Formula m) :
    let d := heavyDir t p q
    chainCoords t (mkGate g p q) =
      (chainCoords (t.sub d) (pick d p q)).image (Coord.cons d) ∪
      (fullCoords (t.sub (!d)) (pick (!d) p q)).image (Coord.cons (!d)) := by
  cases hd : heavyDir t p q <;> cases g <;> simp [mkGate, chainCoords,coordsStep,hd,pick,fullCoords]

private lemma full_gate (g : Bool) (t : TieRule) (p q : Formula m) :
    fullCols t (mkGate g p q) = insert (.conn []) (chainCols t (mkGate g p q)) := by
  cases g <;> rfl

private lemma parts (g : Bool) (t : TieRule) (p q : Formula m) (x : Coord → ℝ) :
    let T := mkGate g p q
    let d := heavyDir t p q
    let H := pick d p q
    let L := pick (!d) p q
    let xH := restrictRow x d
    let xL := restrictRow x (!d)
    energy t T x (chainCols t T) =
      energy (t.sub d) H xH (chainCols (t.sub d) H) +
      energy (t.sub (!d)) L xL (fullCols (t.sub (!d)) L) +
      (if g then (pairing T x (fun k => |colVec t T (.rot []) k|))^2 else 0) := by
  dsimp only
  rw [gateCols]
  unfold energy
  have hf (d : Bool) (A B : Finset Col) : Col.rot [] ∉ A.image (Col.cons d) ∪ B.image (Col.cons (!d)) := by simp
  cases g <;> simp [Finset.union_singleton,Finset.sum_insert (hf _ _ _),dir_sums Col.cons Col.uncons unc_col, pair_pass,add_comm,add_left_comm,add_assoc]

private lemma connector_energy (g : Bool) (t : TieRule) (p q : Formula m) (x : Coord → ℝ) :
    let T := mkGate g p q
    energy t T x (fullCols t T) =
      (pairing T x (fun k => |colVec t T (.conn []) k|))^2 + energy t T x (chainCols t T) := by
  dsimp only
  rw [full_gate]
  unfold energy
  apply Finset.sum_insert
  rw [gateCols]
  cases g <;> simp

private lemma rotate_bound {c s U Z : ℝ} (h : c^2+s^2 ≤ 1) :
    (s*U+c*Z)^2 + 2*(c*U+s*Z)^2 ≤ 2*U^2 + 10*Z^2 := by
  have hbase : (s*U-c*Z)^2 + (c*U+s*Z)^2 ≤ U^2+Z^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg (sq_nonneg U) (sq_nonneg Z))]
  have hterm : (c*Z)^2 ≤ Z^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1-c^2 by nlinarith [sq_nonneg s]) (sq_nonneg Z)]
  nlinarith [sq_nonneg ((s*U-c*Z)-2*(c*Z))]

private lemma connect_bound {c s U Z : ℝ} (h : c^2+s^2 ≤ 1) :
    (c*Z+s*U)^2 ≤ Z^2+U^2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg (sq_nonneg U) (sq_nonneg Z)),
    sq_nonneg (s*Z-c*U)]

private def Bound (t : TieRule) (T : Formula m) (x : Coord → ℝ) : Prop :=
  energy t T x (chainCols t T) + 2 * (uval t T x)^2 ≤ 11 * mass T x ∧
  energy t T x (fullCols t T) + 10 * (x (exportKey T))^2 ≤ 11 * mass T x

private lemma energy_bound (t : TieRule) (T : Formula m) (x : Coord → ℝ) : Bound t T x := by
  have gate (g : Bool) (t : TieRule) (p q : Formula m) (x : Coord → ℝ)
      (hp : ∀ t x, Bound t p x) (hq : ∀ t x, Bound t q x) :
      Bound t (mkGate g p q) x := by
    let d := heavyDir t p q
    let H := pick d p q
    let L := pick (!d) p q
    let tH := t.sub d
    let tL := t.sub (!d)
    let xH := restrictRow x d
    let xL := restrictRow x (!d)
    let U := uval tH H xH
    let Z := xL (exportKey L)
    let E := energy t (mkGate g p q) x (chainCols t (mkGate g p q))
    let u := uval t (mkGate g p q) x
    have hchild (e : Bool) (x' : Coord → ℝ) : Bound (t.sub e) (pick e p q) x' := by
      cases e
      · exact hp _ _
      · exact hq _ _
    have hH := (hchild d xH).1
    have hL := (hchild (!d) xL).2
    change energy tH H xH (chainCols tH H) + 2*U^2 ≤ 11*mass H xH at hH
    change energy tL L xL (fullCols tL L) + 10*Z^2 ≤ 11*mass L xL at hL
    have hs : E + 2*u^2 ≤ 11*(mass H xH + mass L xL) := by
      have hangle := (node_ok g t p q).2.2
      change (ang g t p q).1^2+(ang g t p q).2^2 ≤ 1 at hangle
      have hu : u = (ang g t p q).1*U+(ang g t p q).2*Z := u_pair _ _ _ _ _
      have he := parts g t p q x
      change E = energy tH H xH (chainCols tH H) + energy tL L xL (fullCols tL L) + _ at he
      rw [hu, he]
      cases g with
      | false =>
        simp only [Bool.false_eq_true,if_false,add_zero]
        have hb := connect_bound (U:=Z) (Z:=U) hangle
        nlinarith [sq_nonneg Z]
      | true =>
        simp only [if_true]
        have hr : pairing (mkGate true p q) x (fun k => |colVec t (mkGate true p q) (.rot []) k|) =
          (ang true t p q).2*U+(ang true t p q).1*Z := rot_pair _ _ _ _
        rw [hr]
        linarith [rotate_bound (U:=U) (Z:=Z) hangle]
    have hm : mass (mkGate g p q) x = (x (.helper []))^2 + (mass H xH + mass L xL) :=
      mass_gate g d p q x
    have hkey : exportKey (mkGate g p q) = .helper [] := by cases g <;> rfl
    constructor
    · change E + 2*u^2 ≤ _
      rw [hm]
      linarith [sq_nonneg (x (.helper []))]
    · rw [hm,hkey,connector_energy,conn_pair]
      have hb := connect_bound (U:=u) (Z:=x (.helper []))
        (conn_ok (chainParams t (mkGate g p q)).1 (chainParams t (mkGate g p q)).2).2.2
      change _ + E + _ ≤ _
      linarith [sq_nonneg u]
  induction T generalizing t x with
  | lit i b =>
    simp [Bound,energy,uval,pairing,mass,chainU,colVec,rows,chainCols,fullCols,fullColsOf,
      exportKey, Formula.isLeaf,basisV]
    constructor <;> nlinarith [sq_nonneg (x (.leaf []))]
  | and p q hp hq => exact gate false t p q x hp hq
  | or p q hp hq => exact gate true t p q x hp hq


private lemma row_sets (t : TieRule) (T : Formula m) :
    chainCoords t T ⊆ rows T ∧ fullCoords t T ⊆ rows T := by
  have gate (g : Bool) (t : TieRule) (p q : Formula m)
      (hp : ∀ t, chainCoords t p ⊆ rows p ∧ fullCoords t p ⊆ rows p)
      (hq : ∀ t, chainCoords t q ⊆ rows q ∧ fullCoords t q ⊆ rows q) :
      chainCoords t (mkGate g p q) ⊆ rows (mkGate g p q) ∧
      fullCoords t (mkGate g p q) ⊆ rows (mkGate g p q) := by
    let d := heavyDir t p q
    have sub (e : Bool) : chainCoords (t.sub e) (pick e p q) ⊆ rows (pick e p q) ∧
        fullCoords (t.sub e) (pick e p q) ⊆ rows (pick e p q) := by
      cases e
      · exact hp _
      · exact hq _
    have h : chainCoords t (mkGate g p q) ⊆ rows (mkGate g p q) := by
      rw [gateCoords,gateRows g d]
      exact (Finset.union_subset_union (Finset.image_subset_image (sub d).1)
        (Finset.image_subset_image (sub (!d)).2)).trans (Finset.subset_insert _ _)
    refine ⟨h,?_⟩
    have e : fullCoords t (mkGate g p q) = insert (.helper []) (chainCoords t (mkGate g p q)) := by
      cases g <;> rfl
    rw [e, Finset.insert_subset_iff]
    exact ⟨by simp [gateRows g d,pairRows],h⟩
  induction T generalizing t with
  | lit i b => simp [chainCoords, fullCoords,fullCoordsOf,Formula.isLeaf,rows]
  | and p q hp hq => exact gate false t p q hp hq
  | or p q hp hq => exact gate true t p q hp hq

private lemma dual_bound (t : TieRule) (T : Formula m) (x : fullCoords t T → ℝ) :
    ∑ j : fullCols t T, (∑ k : fullCoords t T, x k * |colVec t T j.val k.val|)^2 ≤
    11 * ∑ k : fullCoords t T, (x k)^2 := by
  classical
  let X := fun k : Coord => if h : k ∈ fullCoords t T then x ⟨k,h⟩ else 0
  have restrict (f : Coord → ℝ) (hf : ∀ k, k ∉ fullCoords t T → f k = 0) :
      ∑ k ∈ rows T, f k = ∑ k : fullCoords t T, f k.val :=
    (Finset.sum_subset (row_sets t T).2 (fun k _ hk => hf k hk)).symm.trans
      (Finset.sum_subtype (fullCoords t T) (fun _ => Iff.rfl) f)
  have hm : mass T X = ∑ k : fullCoords t T, (x k)^2 := by
    unfold mass
    rw [restrict _ (by intro k hk; simp [X,hk])]
    simp [X]
  have hp (j : Col) : pairing T X (fun k => |colVec t T j k|) =
      ∑ k : fullCoords t T, x k * |colVec t T j k.val| := by
    unfold pairing
    rw [restrict _ (by intro k hk; simp [X,hk])]
    simp [X]
  have he := (energy_bound t T X).2
  have h : energy t T X (fullCols t T) ≤ 11 * mass T X := by
    linarith [sq_nonneg (X (exportKey T))]
  unfold energy at h
  rw [Finset.sum_subtype (fullCols t T) (fun _ => Iff.rfl),hm] at h
  simpa only [hp] using h

private lemma from_dual {ι J : Type} [Fintype ι] [Fintype J] (V : J → ι → ℝ)
    (h : ∀ x : ι → ℝ, (∑ j, (∑ i, x i * |V j i|)^2) ≤ 11 * ∑ i, (x i)^2) :
    AbsNormLE V (Real.sqrt 11) := by
  classical
  intro y
  let b := fun i => ∑ j, |V j i| * y j
  let a := fun j => ∑ i, b i * |V j i|
  have he : ∑ i, (b i)^2 = ∑ j, a j * y j := by
    calc
      _ = ∑ i, b i * (∑ j, |V j i| * y j) := by simp only [sq]; rfl
      _ = _ := by simp only [a, Finset.mul_sum, Finset.sum_mul, mul_assoc]; rw [Finset.sum_comm]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a y
  rw [← he] at hcs
  have hdual : ∑ j, (a j)^2 ≤ 11 * ∑ i, (b i)^2 := h b
  have hy : 0 ≤ ∑ j, (y j)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hb : 0 ≤ ∑ i, (b i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hle : ∑ i, (b i)^2 ≤ 11 * ∑ j, (y j)^2 := by
    by_contra! hlt
    have hpos : 0 < ∑ i, (b i)^2 := by linarith
    nlinarith [mul_pos (sub_pos.mpr hlt) hpos, mul_le_mul_of_nonneg_right hdual hy]
  exact (Real.sqrt_le_sqrt hle).trans_eq (Real.sqrt_mul (by norm_num) _)

end ChainEnergy

open ChainEnergy

theorem solution :
    ∃ c : ℝ, ∀ (m : ℕ) (tie : TieRule) (T : Formula m), AbsNormLE (program tie T).vec c := by
  refine ⟨Real.sqrt 11, fun m t T => from_dual _ ?_⟩
  exact dual_bound t T
