-- Prove2me | solution 1 for DirectedHamiltonicity.Main.prepare_cycle_parity_query_poly
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-27T02:22:03.133472+00:00
-- url     : https://prove2.me/submissions/e6252cb3-7d3a-4b91-a6bd-7ecb4571b98b

import Definitions.Def_DirectedHamiltonicity_CycleSearch
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

namespace DirectedHamiltonicity.Main.CycleReduction.NativeQuery

open Multidigraph

def rows {n : ℕ} (adj : Fin n → Fin n → Bool) : List (List Bool) :=
  List.ofFn fun u => List.ofFn (adj u)

def atArc (G : List (List Bool)) (u v : ℕ) : Bool :=
  ((G[u]?.getD [])[v]?).getD false

@[simp] theorem rows_length {n : ℕ} (adj : Fin n → Fin n → Bool) : (rows adj).length = n := by simp [rows]

@[simp] theorem atArc_rows {n : ℕ} (adj : Fin n → Fin n → Bool) (u v : Fin n) :
    atArc (rows adj) u.val v.val = adj u v := by simp [atArc,rows]

/-- The two table ranks precede the target weight, and the endpoint rank precedes both tables. -/
def tableRadix (n : ℕ) := Wmax n ^ (n*3)
def endRadix (n : ℕ) := (50^(n*n)*tableRadix n)*(Bmax n+1)
def source (n word : ℕ) := (word / endRadix n) / n
def sink (n word : ℕ) := (word / endRadix n) % n
def target (n word : ℕ) := (word % endRadix n) % (Bmax n+1)
def tables (n word : ℕ) := (word % endRadix n) / (Bmax n+1)
def symbol (n word u v : ℕ) := ((tables n word / tableRadix n) / 50^(v+n*u)) % 50
def groupValue (n word v g : ℕ) := ((tables n word % tableRadix n) / (Wmax n)^(g+3*v)) % Wmax n + 1
def chosen (m g : ℕ) : Bool := (if m=0 then 0 else 1+(m-1)/7).testBit g

theorem source_digit {n : ℕ} (w : Fin (drawCount n)) : ((rankDraw n).symm w).1.1.val = source n w := rfl
theorem sink_digit {n : ℕ} (w : Fin (drawCount n)) : ((rankDraw n).symm w).1.2.val = sink n w := rfl
theorem target_digit {n : ℕ} (w : Fin (drawCount n)) : ((rankDraw n).symm w).2.2.val = target n w := rfl
theorem mask_digit {n : ℕ} (w : Fin (drawCount n)) (u v : Fin n) :
    (((rankDraw n).symm w).2.1.1 (u,v)).val = symbol n w u v := rfl
theorem weight_digit {n : ℕ} (w : Fin (drawCount n)) (v : Fin n) (g : Fin 3) :
    (((rankDraw n).symm w).2.1.2 (v,g)).val+1 = groupValue n w v g := rfl

def triple (G : List (List Bool)) (word i : ℕ) : ℕ × ℕ × ℕ :=
  let n := G.length
  let u := (i/3)/n
  let v := (i/3)%n
  let g := i%3
  let s := source n word
  let t := sink n word
  if atArc G u v = true ∧ u ≠ v ∧ v ≠ s ∧ u ≠ t ∧ chosen (symbol n word u v) g = true
  then (u,v,groupValue n word v g) else (s,s,0)

def fieldTriple (e : ℕ × ℕ × ℕ) := encNat e.1 ++ encNat e.2.1 ++ encNat e.2.2

/-- Serialize a raw rank by division and remainders, using one row of three slots per ordered pair. -/
def build (G : List (List Bool)) (word : ℕ) : Option (List Bool) :=
  let n := G.length
  let s := source n word
  let t := sink n word
  if word < drawCount n ∧ s ≠ t ∧ atArc G t s = true then
    some (encNat n ++ encNat (n*n*3) ++ ((List.range (n*n*3)).flatMap fun i => fieldTriple (triple G word i)) ++
      encNat s ++ encNat t ++ encInt (target n word))
  else none

theorem triple_exact {n : ℕ} (adj : Fin n → Fin n → Bool) (w : Fin (drawCount n)) (i : Fin (n*n*3)) :
    let z := (rankDraw n).symm w
    let s := z.1.1
    let t := z.1.2
    let a := pathAdj adj s t
    let r := restrictedSeed a s z.2.1
    let S := fun e => copyMask (r.1 e)
    let H := inputGraph a S s
    triple (rows adj) w i = ((H.tail i).val, (H.head i).val, inputWeight a S s (clean_no_in adj s t) (labelWeight s r.2) i) := by
  let z := (rankDraw n).symm w
  let p := (slotEquiv n).symm i
  let u := p.1.1
  let v := p.1.2
  let g := p.2
  let s := z.1.1
  let t := z.1.2
  let a := pathAdj adj s t
  let r := restrictedSeed a s z.2.1
  let S := fun e => copyMask (r.1 e)
  let wt := labelWeight s r.2
  let d := decodeSlot a S i
  change _ = ((d.elim s (copyGraph a S).tail).val,(d.elim s (copyGraph a S).head).val,
    d.elim 0 (GroupIsolation.weight a S s (clean_no_in adj s t) wt))
  have U : (i.val/3)/n = u.val := rfl
  have V : (i.val/3)%n = v.val := rfl
  have J : i.val%3 = g.val := rfl
  simp only [triple,rows_length,U,V,J,atArc_rows,← source_digit,← sink_digit]
  change (if adj u v = true ∧ u.val ≠ v.val ∧ v.val ≠ s.val ∧ u.val ≠ t.val ∧
    chosen (symbol n w u.val v.val) g.val = true then _ else _) = _
  have mask (h : a u v) : g ∈ S ⟨(u,v),h⟩ ↔ chosen (symbol n w u v) g = true := by
    change g ∈ (Finset.univ.filter fun j : Fin 3 => chosen (z.2.1.1 (u,v)).val j.val = true) ↔ _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [show (z.2.1.1 (u,v)).val = symbol n w u v from mask_digit w u v]
  by_cases ha : a u v
  · by_cases hm : g ∈ S ⟨(u,v),ha⟩
    · have ok := (mask ha).1 hm
      rw [if_pos ⟨ha.1,fun e => ha.2.1 (Fin.ext e),fun e => ha.2.2.1 (Fin.ext e),fun e => ha.2.2.2 (Fin.ext e),ok⟩]
      have hd : d = some ⟨⟨(u,v),ha⟩,g,hm⟩ := by
        change decodePair a S ((u,v),g) = _
        simp [decodePair,ha,hm]
      rw [hd]
      exact Prod.ext rfl (Prod.ext rfl (weight_digit w v g).symm)
    · have no : ¬chosen (symbol n w u v) g = true := fun e => hm ((mask ha).2 e)
      rw [if_neg (fun h => no h.2.2.2.2)]
      have hd : d = none := by
        change decodePair a S ((u,v),g) = _
        simp [decodePair,ha,hm]
      rw [hd];rfl
  · rw [if_neg (fun h => ha ⟨h.1,fun e => h.2.1 (congrArg Fin.val e),fun e => h.2.2.1 (congrArg Fin.val e),
        fun e => h.2.2.2.1 (congrArg Fin.val e)⟩)]
    have hd : d = none := by
      change decodePair a S ((u,v),g) = _
      simp [decodePair,ha]
    rw [hd];rfl

private theorem serialize_eq {n m : ℕ} (fields : ℕ → ℕ × ℕ × ℕ) (a b : Fin m → Fin n)
    (weight : Fin m → ℕ) (s t : Fin n) (B : ℕ)
    (equal : ∀ i : Fin m, fields i.val = ((a i).val,(b i).val,weight i)) :
    encNat n ++ encNat m ++ (List.range m).flatMap (fun i => fieldTriple (fields i)) ++ encNat s.val ++
      encNat t.val ++ encInt B = encodeParityInstance n m a b weight s t B := by
  have seq : List.range m = (List.finRange m).map Fin.val := by
    apply List.ext_getElem <;> simp
  have record : (List.range m).flatMap (fun i => fieldTriple (fields i)) =
      (List.finRange m).flatMap (fun i => encNat (a i).val ++ encNat (b i).val ++ encNat (weight i)) := by
    rw [seq,List.flatMap_map]
    apply congrArg (fun f => (List.finRange m).flatMap f)
    funext i
    change fieldTriple (fields i.val) = _
    rw [equal i]; rfl
  rw [record]; rfl

theorem build_exact {n : ℕ} (adj : Fin n → Fin n → Bool) (word : ℕ) :
    build (rows adj) word =
      if h : word < drawCount n then candidateInput adj ((rankDraw n).symm ⟨word,h⟩) else none := by
  by_cases h : word < drawCount n
  · let w : Fin (drawCount n) := ⟨word,h⟩
    let z := (rankDraw n).symm w
    let s := z.1.1
    let t := z.1.2
    have S : source n word = s.val := (source_digit w).symm
    have T : sink n word = t.val := (sink_digit w).symm
    have B : target n word = z.2.2.val := (target_digit w).symm
    simp only [build,rows_length,dif_pos h,h,true_and,S,T,atArc_rows,B]
    by_cases ok : s ≠ t ∧ adj t s = true
    · have valid : s.val ≠ t.val ∧ adj t s = true := ⟨fun e => ok.1 (Fin.ext e),ok.2⟩
      rw [if_pos valid]
      change _ = (if s ≠ t ∧ adj t s = true then _ else _)
      rw [if_pos ok]
      apply congrArg some
      apply serialize_eq
      exact triple_exact adj w
    · have invalid : ¬(s.val ≠ t.val ∧ adj t s = true) := fun q => ok ⟨fun e => q.1 (congrArg Fin.val e),q.2⟩
      rw [if_neg invalid]
      change _ = (if s ≠ t ∧ adj t s = true then _ else _)
      rw [if_neg ok]
  · simp [build,rows_length,h]

end DirectedHamiltonicity.Main.CycleReduction.NativeQuery

namespace DirectedHamiltonicity.Main.CycleReduction.NativeQuery

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

abbrev Matrix := List (List Bool)

/-- A polynomial-length list of slots in the explicit input matrix. -/
def fuel (G : Matrix) : List ℕ := G.flatMap fun _ => G.flatMap fun _ => [0,0,0]

@[simp] theorem fuel_len (G : Matrix) : (fuel G).length = G.length*G.length*3 := by
  have inner : (G.flatMap fun _ => ([0,0,0] : List ℕ)).length = G.length*3 := by
    induction G with
    | nil => rfl
    | cons x xs ih => simp [List.flatMap_cons,ih,Nat.succ_mul]
  let row := G.flatMap fun _ => ([0,0,0] : List ℕ)
  have repeat_len (xs : Matrix) : (xs.flatMap fun _ => row).length = xs.length*row.length := by
    induction xs with
    | nil => simp
    | cons a xs ih => simp [List.flatMap_cons,ih,Nat.succ_mul,Nat.add_comm]
  change (G.flatMap fun _ => row).length = _
  rw [repeat_len,show row.length=G.length*3 from inner]; ring

variable {I : Type} [Coding I] [Inhabited I]

@[local fun_prop] private theorem add {a b : I → ℕ} (ha : Poly a) (hb : Poly b) :
    Poly (fun x => a x+b x) := Poly.comp Poly.nat_add (Poly.pair ha hb)
@[local fun_prop] private theorem sub {a b : I → ℕ} (ha : Poly a) (hb : Poly b) :
    Poly (fun x => a x-b x) := Poly.comp Poly.nat_sub (Poly.pair ha hb)
@[local fun_prop] private theorem mul {a b : I → ℕ} (ha : Poly a) (hb : Poly b) :
    Poly (fun x => a x*b x) := Poly.comp Poly.nat_mul (Poly.pair ha hb)
@[local fun_prop] private theorem div {a b : I → ℕ} (ha : Poly a) (hb : Poly b) :
    Poly (fun x => a x/b x) := Poly.comp (f := fun x : ℕ × ℕ => x.1/x.2) ⟨PolyProgram.natDiv⟩ (Poly.pair ha hb)
@[local fun_prop] private theorem modN {a b : I → ℕ} (ha : Poly a) (hb : Poly b) :
    Poly (fun x => a x%b x) := Poly.comp (f := fun x : ℕ × ℕ => x.1%x.2) ⟨PolyProgram.natMod⟩ (Poly.pair ha hb)
@[local fun_prop] private theorem cons {α : Type} [Coding α] {a : I → α} {b : I → List α} (ha : Poly a) (hb : Poly b) :
    Poly (fun x => a x::b x) := Poly.comp Poly.list_cons (Poly.pair ha hb)
@[local fun_prop] private theorem append {α : Type} [Coding α] [Inhabited α] {a b : I → List α} (ha : Poly a) (hb : Poly b) :
    Poly (fun x => a x++b x) := Poly.comp Poly.list_append (Poly.pair ha hb)
@[local fun_prop] private theorem andDec {p q : I → Prop} [DecidablePred p] [DecidablePred q]
    (hp : Poly (fun x => decide (p x))) (hq : Poly (fun x => decide (q x))) :
    Poly (fun x => decide (p x ∧ q x)) := by
  have eq : (fun x => decide (p x ∧ q x)) = fun x => decide (p x) && decide (q x) := by
    funext x;by_cases a : p x <;> by_cases b : q x <;> simp [a,b]
  rw [eq]; exact Poly.comp Poly.bool_and (Poly.pair hp hq)
@[local fun_prop] private theorem neDec {a b : I → ℕ} (ha : Poly a) (hb : Poly b) :
    Poly (fun x => decide (a x ≠ b x)) := by
  simp only [ne_eq,decide_not];exact Poly.comp Poly.bool_not (Poly.nat_eq_comp ha hb)
@[local fun_prop] private theorem boolTrue {p : I → Bool} (hp : Poly p) :
    Poly (fun x => decide (p x = true)) := by simpa using hp
@[local fun_prop] private theorem polyFuel {G : I → Matrix} (hg : Poly G) : Poly (fun x => fuel (G x)) := by
  unfold fuel;fun_prop
@[local fun_prop] private theorem len {α : Type} [Coding α] [Inhabited α] {f : I → List α} (h : Poly f) :
    Poly (fun x => (f x).length) := Poly.comp Poly.list_length h

private theorem prodPoly {f : I → List ℕ} (h : Poly f) : Poly (fun x => (f x).prod) := by
  let q : List ℕ → ℕ := fun xs => ((xs.map fun y : ℕ => (y:ℚ)).prod).num.natAbs
  have swap (xs : List ℕ) : (xs.map fun y : ℕ => (y:ℚ)).prod=(xs.prod:ℚ) := by
    induction xs with
    | nil => simp
    | cons y ys ih => simp only [List.map_cons,List.prod_cons,Nat.cast_mul,ih]
  have eq : (fun x => (f x).prod) = (fun x => q (f x)) := by funext x;simp only [q,swap,Rat.num_natCast,Int.natAbs_natCast]
  rw [eq]
  exact Poly.comp (f := Int.natAbs) ⟨PolyProgram.intAbs⟩ (Poly.comp (f := Rat.num) ⟨PolyProgram.ratNum⟩
    (Poly.comp (f := (List.prod : List ℚ → ℚ)) ⟨PolyProgram.ratProd⟩
      (Poly.list_map (f := fun (_ : I) (n : ℕ) => (n:ℚ)) (Poly.comp Poly.rat_ofNat Poly.snd) h)))

private theorem boundedPow {G : I → Matrix} {base e : I → ℕ} (hg : Poly G) (hb : Poly base) (he : Poly e)
    (bound : ∀ x,(e x)≤(fuel (G x)).length) : Poly (fun x => base x ^ e x) := by
  let take := fun x => (fuel (G x)).take (e x)
  have ht : Poly take := Poly.comp QMCNumericRuntime.parser_take_poly (Poly.pair (polyFuel hg) he)
  have same (xs : List ℕ) (v : ℕ) : (xs.map fun _ => v).prod = v^xs.length := by
    induction xs with
    | nil => simp
    | cons y ys ih => simp [ih,pow_succ']
  have eq : (fun x => base x ^ e x) = fun x => ((take x).map fun _ => base x).prod := by
    funext x; simp only [same,take,List.length_take,Nat.min_eq_left (bound x)]
  rw [eq]
  exact prodPoly (Poly.list_map (f := fun x (_ : ℕ) => base x) (Poly.comp hb Poly.fst) ht)

@[local fun_prop] private theorem tablePoly {G : I → Matrix} (hg : Poly G) :
    Poly (fun x => tableRadix (G x).length) := by
  unfold tableRadix Wmax
  apply boundedPow hg (by fun_prop) (by fun_prop)
  intro x
  simp only [fuel_len]
  cases (G x).length with
  | zero => simp
  | succ n => nlinarith

@[local fun_prop] private theorem endPoly {G : I → Matrix} (hg : Poly G) :
    Poly (fun x => endRadix (G x).length) := by
  have maskPower : Poly (fun x => 50^((G x).length*(G x).length) : I → ℕ) :=
    boundedPow hg (Automatic.Poly.const 50) (by fun_prop) (fun x => by rw [fuel_len];omega)
  unfold endRadix Bmax Wmax
  fun_prop

@[local fun_prop] private theorem sourcePoly {G : I → Matrix} {w : I → ℕ} (hg : Poly G) (hw : Poly w) :
    Poly (fun x => source (G x).length (w x)) := by unfold source;fun_prop
@[local fun_prop] private theorem sinkPoly {G : I → Matrix} {w : I → ℕ} (hg : Poly G) (hw : Poly w) :
    Poly (fun x => sink (G x).length (w x)) := by unfold sink;fun_prop
@[local fun_prop] private theorem tablesPoly {G : I → Matrix} {w : I → ℕ} (hg : Poly G) (hw : Poly w) :
    Poly (fun x => tables (G x).length (w x)) := by unfold tables Bmax Wmax;fun_prop
@[local fun_prop] private theorem targetPoly {G : I → Matrix} {w : I → ℕ} (hg : Poly G) (hw : Poly w) :
    Poly (fun x => target (G x).length (w x)) := by unfold target Bmax Wmax;fun_prop

@[local fun_prop] private theorem testPoly {x j : I → ℕ} (hx : Poly x) (hj : Poly j) :
    Poly (fun a => (x a).testBit (j a)) := by
  have bits (v i : ℕ) : v.bits[i]?.getD false = v.testBit i := by
    induction i generalizing v with
    | zero =>
      cases v using Nat.binaryRec' with
      | zero => rfl
      | bit b v nonzero => simp [Nat.bits_append_bit _ _ nonzero,Nat.testBit_bit_zero]
    | succ i ih =>
      cases v using Nat.binaryRec' with
      | zero => simp
      | bit b v nonzero => simpa [Nat.bits_append_bit _ _ nonzero,Nat.testBit_bit_succ] using ih v
  simp_rw [←bits]
  exact Poly.list_getD_comp false (Poly.comp (f := Nat.bits) ⟨PolyProgram.natAsList⟩ hx) hj

@[local fun_prop] private theorem choicePoly {m j : I → ℕ} (hm : Poly m) (hj : Poly j) :
    Poly (fun x => chosen (m x) (j x)) := by unfold chosen;fun_prop


@[local fun_prop] private theorem arcPoly {G : I → Matrix} {u v : I → ℕ}
    (hg : Poly G) (hu : Poly u) (hv : Poly v) : Poly (fun x => atArc (G x) (u x) (v x)) := by
  unfold atArc; fun_prop

private theorem symPoly {G : I → Matrix} {w u v : I → ℕ} (hg : Poly G) (hw : Poly w)
    (hu : Poly u) (hv : Poly v) (h : ∀ x, v x+(G x).length*u x ≤ (fuel (G x)).length) :
    Poly (fun x => symbol (G x).length (w x) (u x) (v x)) := by
  have p : Poly (fun x => 50^(v x+(G x).length*u x) : I → ℕ) := boundedPow hg (by fun_prop) (by fun_prop) h
  unfold symbol;fun_prop

private theorem groupPoly {G : I → Matrix} {w v g : I → ℕ} (hg : Poly G) (hw : Poly w)
    (hv : Poly v) (hj : Poly g) (h : ∀ x, g x+3*v x ≤ (fuel (G x)).length) :
    Poly (fun x => groupValue (G x).length (w x) (v x) (g x)) := by
  have p : Poly (fun x => Wmax (G x).length^(g x+3*v x)) := boundedPow hg (by unfold Wmax;fun_prop) (by fun_prop) h
  unfold groupValue
  apply add
  · apply modN
    · apply div (by fun_prop) p
    · unfold Wmax;fun_prop
  · fun_prop

def safeSlot (G : Matrix) (i : ℕ) : ℕ := i % (G.length*G.length*3+1)

@[local fun_prop] private theorem safePoly {G : I → Matrix} {i : I → ℕ} (hg : Poly G) (hi : Poly i) :
    Poly (fun x => safeSlot (G x) (i x)) := by unfold safeSlot;fun_prop

@[local fun_prop] private theorem triplePoly {G : I → Matrix} {w i : I → ℕ} (hg : Poly G)
    (hw : Poly w) (hi : Poly i) :
    Poly (fun x => triple (G x) (w x) (safeSlot (G x) (i x))) := by
  let j := fun x => safeSlot (G x) (i x)
  let u := fun x => (j x/3)/(G x).length
  let v := fun x => (j x/3)%(G x).length
  let g := fun x => j x%3
  have pj : Poly j := safePoly hg hi
  have pu : Poly u := div (div pj (by fun_prop)) (len hg)
  have pv : Poly v := modN (div pj (by fun_prop)) (len hg)
  have pg : Poly g := modN pj (by fun_prop)
  have le (x) : j x ≤ (fuel (G x)).length := by
    rw [fuel_len]; exact Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos _))
  have ps := symPoly hg hw pu pv (fun x => by
    change (j x/3)%(G x).length+(G x).length*((j x/3)/(G x).length) ≤ _
    rw [Nat.mod_add_div];exact (Nat.div_le_self _ _).trans (le x))
  have pw := groupPoly hg hw pv pg (fun x => by
    change j x%3+3*((j x/3)%(G x).length) ≤ _
    calc
      _ ≤ j x%3+3*(j x/3) := Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mod_le _ _)) _
      _ = _ := Nat.mod_add_div _ _
      _ ≤ _ := le x)
  change Poly (fun x => if atArc (G x) (u x) (v x) = true ∧ u x ≠ v x ∧
    v x ≠ source (G x).length (w x) ∧ u x ≠ sink (G x).length (w x) ∧
    chosen (symbol (G x).length (w x) (u x) (v x)) (g x) = true
    then (u x,v x,groupValue (G x).length (w x) (v x) (g x))
    else (source (G x).length (w x),source (G x).length (w x),0))
  apply Poly.ite_prop
  · apply andDec (boolTrue (arcPoly hg pu pv))
    apply andDec (neDec pu pv)
    apply andDec (neDec pv (sourcePoly hg hw))
    exact andDec (neDec pu (sinkPoly hg hw)) (boolTrue (choicePoly ps pg))
  · exact Poly.pair pu (Poly.pair pv pw)
  · fun_prop

@[local fun_prop] private theorem natCode {a : I → ℕ} (ha : Poly a) :
    Poly (fun x => encNat (a x)) := by
  unfold encNat
  apply append
  · apply Poly.list_flatMap (f := fun (_ : I) (b : Bool) => [true,b])
    · fun_prop
    · exact Poly.comp (f := Nat.bits) ⟨PolyProgram.natAsList⟩ ha
  · fun_prop

@[local fun_prop] private theorem fieldsPoly {f : I → ℕ × ℕ × ℕ} (h : Poly f) :
    Poly (fun x => fieldTriple (f x)) := by unfold fieldTriple;fun_prop

private theorem flatMap_agree {α β : Type} (xs : List α) (f g : α → List β) (h : ∀ i∈xs, f i = g i) :
    xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.flatMap_cons,h a (List.mem_cons_self ..),ih (fun i m => h i (List.mem_cons_of_mem _ m))]

private theorem recordStream {G : I → Matrix} {w : I → ℕ} (hg : Poly G) (hw : Poly w) :
    Poly (fun x => (List.range ((G x).length*(G x).length*3)).flatMap (fun i => fieldTriple (triple (G x) (w x) i))) := by
  let places := fun x => List.range (fuel (G x)).length
  have pl : Poly places := Poly.comp (f := fun xs : List ℕ => List.range xs.length) Poly.list_indices (polyFuel hg)
  have same : (fun x => (List.range ((G x).length*(G x).length*3)).flatMap (fun i => fieldTriple (triple (G x) (w x) i))) =
      fun x => (places x).flatMap (fun i => fieldTriple (triple (G x) (w x) (safeSlot (G x) i))) := by
    funext x;dsimp only [places];rw [fuel_len]
    apply flatMap_agree
    intro i hi
    rw [safeSlot,Nat.mod_eq_of_lt (Nat.lt.step (List.mem_range.mp hi))]
  rw [same]
  apply Poly.list_flatMap (f := fun x i => fieldTriple (triple (G x) (w x) (safeSlot (G x) i))) _ pl
  exact fieldsPoly (triplePoly (Poly.comp hg Poly.fst) (Poly.comp hw Poly.fst) Poly.snd)

private theorem allWords {G : I → Matrix} {w : I → ℕ} (hg : Poly G) (hw : Poly w) :
    Poly (fun x => ((build (G x) (w x)).getD [])) := by
  have count : Poly (fun x => drawCount (G x).length) := by
    change Poly (fun x => (G x).length*(G x).length*endRadix (G x).length)
    fun_prop
  have stream := recordStream hg hw
  have eq : (fun x => ((build (G x) (w x)).getD [])) = fun x =>
      if w x < drawCount (G x).length ∧ source (G x).length (w x) ≠ sink (G x).length (w x) ∧
          atArc (G x) (sink (G x).length (w x)) (source (G x).length (w x)) = true then
        encNat (G x).length ++ encNat ((G x).length*(G x).length*3) ++
          (List.range ((G x).length*(G x).length*3)).flatMap (fun i => fieldTriple (triple (G x) (w x) i)) ++
          encNat (source (G x).length (w x)) ++ encNat (sink (G x).length (w x)) ++
          (false :: encNat (target (G x).length (w x))) else [] := by
    funext x
    by_cases v : w x < drawCount (G x).length ∧ source (G x).length (w x) ≠ sink (G x).length (w x) ∧
      atArc (G x) (sink (G x).length (w x)) (source (G x).length (w x)) = true
    · simp only [build,if_pos v,Option.getD_some,encInt,Int.natAbs_natCast]
      have sign : ¬((target (G x).length (w x):ℤ)<0) := by exact_mod_cast (Nat.not_lt_zero _)
      rw [decide_eq_false sign]
    · simp only [build,if_neg v,Option.getD_none]
  rw [eq]
  apply Poly.ite_prop
  · exact andDec (Poly.nat_lt_comp hw count) (andDec (neDec (sourcePoly hg hw) (sinkPoly hg hw))
      (boolTrue (arcPoly hg (sinkPoly hg hw) (sourcePoly hg hw))))
  · fun_prop
  · fun_prop

/-- A single polynomial-time binary program prepares the exact weighted instance from a
materialized adjacency matrix and a raw trial rank. The empty string encodes a skipped call. -/
theorem prepare_query_poly : Poly (fun x : Matrix × ℕ => (build x.1 x.2).getD []) :=
  allWords Poly.fst Poly.snd

end DirectedHamiltonicity.Main.CycleReduction.NativeQuery

open DirectedHamiltonicity.Main DirectedHamiltonicity.Main.CycleReduction

theorem solution :
    ∃ prepare : List (List Bool) × ℕ → List Bool, OAI.MetricKMedian.Binary.Automatic.Poly prepare ∧
      ∀ (n : ℕ) (adj : Fin n → Fin n → Bool) (word : ℕ),
        prepare (List.ofFn (fun u => List.ofFn (adj u)),word) =
          if h : word < drawCount n then (candidateInput adj ((rankDraw n).symm ⟨word,h⟩)).getD [] else [] := by
  refine ⟨_,NativeQuery.prepare_query_poly,?_⟩
  intro n adj word
  change (NativeQuery.build (NativeQuery.rows adj) word).getD [] = _
  rw [NativeQuery.build_exact]
  split <;> rfl
