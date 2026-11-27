-- Prove2me | solution 1 for DirectedHamiltonicity.Main.prepare_cycle_parity_query_ram
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-27T02:28:38.565404+00:00
-- url     : https://prove2.me/submissions/f9f2ddb3-c7ab-4139-b38c-5b31be30d383

import Theorems.Thm_DirectedHamiltonicity_Main_prepare_cycle_parity_query_poly
import Theorems.Thm_TargetedSamplers_Structured_StackMachine_fields_call
import Definitions.Def_LogCostRAM_StructuredExecution
import Definitions.Def_DirectedHamiltonicity_CycleSearch

namespace TargetedSamplers.NumericFields

theorem bounds (w : ℕ) (xs : List ℕ) (h : ∀ x∈xs,x<2^w) :
    2^(w*xs.length) ≤ pack w xs ∧ pack w xs < 2^(w*xs.length+1) := by
  induction xs with
  | nil => simp [pack,join]
  | cons x xs ih =>
    have digit := h x (by simp)
    obtain ⟨low,high⟩ := ih (fun a ha => h a (by simp [ha]))
    have pos := Nat.two_pow_pos w
    have scaled := Nat.mul_le_mul_left (2^w) low
    have scaledTop := Nat.mul_le_mul_left (2^w) (Nat.succ_le_of_lt high)
    change _ ≤ x+2^w*pack w xs ∧ x+2^w*pack w xs < _
    rw [List.length_cons,Nat.mul_succ,Nat.add_comm (w*xs.length) w, pow_add,
      Nat.add_assoc w (w*xs.length) 1,pow_add]
    rw [Nat.mul_succ] at scaledTop
    omega

theorem pack_size (w : ℕ) (xs : List ℕ) (h : ∀ x∈xs,x<2^w) : (pack w xs).size=w*xs.length+1 := by
  obtain ⟨lo,hi⟩ := bounds w xs h
  apply Nat.le_antisymm (Nat.size_le.mpr hi)
  by_contra! small
  have up := Nat.pow_le_pow_right (by decide : 0<2) (by omega : (pack w xs).size≤w*xs.length)
  have pos := Nat.lt_size_self (pack w xs)
  omega


end TargetedSamplers.NumericFields

namespace DirectedHamiltonicity.Main.CycleReduction.QueryRAM

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TargetedSamplers TargetedSamplers.Structured Word BinaryStack NumericFields

def width (z : ℕ) := (z.size-1)/3

def radix (z : ℕ) := QMCNumericRuntime.bitValue (((z.bits.take (width z)).map fun _ => false) ++ [true])

def nVal (z : ℕ) := z % radix z
def graphWord (z : ℕ) := (z/radix z) % radix z
def trialWord (z : ℕ) := ((z/radix z)/radix z) % radix z
def verts (z : ℕ) := (List.range z.bits.length).take (nVal z)
def matrix (z : ℕ) := (verts z).map fun u => (verts z).map fun v =>
  (graphWord z).bits[v+nVal z*u]?.getD false

private theorem sentinel (xs : List Bool) : QMCNumericRuntime.bitValue (xs++[true]) = packed xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [QMCNumericRuntime.bitValue,packed,ih,Nat.bit, Nat.mul_comm,Nat.add_comm]

private theorem zeros (xs : List Bool) : QMCNumericRuntime.bitValue ((xs.map fun _ => false)++[true])=2^xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [List.map_cons,List.cons_append,QMCNumericRuntime.bitValue,Bool.toNat_false,Nat.zero_add,ih,List.length_cons,pow_succ']

theorem radix_eq (z : ℕ) : radix z = 2^(width z) := by
  have short : width z ≤ z.bits.length := by
    rw [Nat.size_eq_bits_len]
    exact (Nat.div_le_self ..).trans (Nat.sub_le ..)
  simp only [radix,zeros,List.length_take,Nat.min_eq_left short]

private theorem unpack (w n a r : ℕ) (hn : n<2^w) (ha : a<2^w) (hr : r<2^w) :
    let z := pack w [n,a,r]
    nVal z=n ∧ graphWord z=a ∧ trialWord z=r ∧ z.bits.length = w*3+1 := by
  let z := pack w [n,a,r]
  have size : z.size=w*3+1 := pack_size w [n,a,r] (by simpa using And.intro hn (And.intro ha hr))
  have base : radix z = 2^w := by rw [radix_eq,width,size];simp
  change nVal z=n ∧ graphWord z=a ∧ trialWord z=r ∧ z.bits.length = _
  rw [nVal,graphWord,trialWord,base,Nat.size_eq_bits_len,size]
  have pos := Nat.two_pow_pos w
  dsimp only [z,pack,join]
  simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hn,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hr,
    Nat.add_mul_div_left _ _ pos,Nat.div_eq_of_lt hn,Nat.div_eq_of_lt ha,Nat.zero_add,and_self]

theorem matrix_pack {n : ℕ} (adj : Fin n → Fin n → Bool) (w a r : ℕ) (nw : n≤w)
    (hn : n<2^w) (ha : a<2^w) (hr : r<2^w) (graph : ∀ u v : Fin n, a.testBit (v.val+n*u.val)=adj u v) :
    matrix (pack w [n,a,r]) = List.ofFn fun u => List.ofFn (adj u) := by
  let z := pack w [n,a,r]
  obtain ⟨dim,value,_,room⟩ := unpack w n a r hn ha hr
  have labels : verts z = List.range n := by
    change (List.range z.bits.length).take (nVal z) = _
    change nVal z=n at dim
    change z.bits.length = _ at room
    rw [dim,room,List.take_range,Nat.min_eq_left (by omega)]
  change (verts z).map (fun u => (verts z).map (fun v => (graphWord z).bits[v+nVal z*u]?.getD false)) = _
  change graphWord z=a at value
  rw [labels,value,dim]
  apply List.ext_getElem
  · simp
  · intro u hu ht
    apply List.ext_getElem
    · simp [List.getElem_map]
    · intro v hv hh
      have U : u<n := by simpa using hu
      have V : v<n := by simpa using hh
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
      have bit := graph ⟨u,U⟩ ⟨v,V⟩
      rw [Nat.testBit_eq_inth,List.getI_eq_getElem?_getD] at bit
      exact bit

variable {I : Type} [Coding I] [Inhabited I]
@[local fun_prop] private theorem sub {f g : I → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x-g x) := Poly.comp Poly.nat_sub (Poly.pair hf hg)
@[local fun_prop] private theorem add {f g : I → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x+g x) := Poly.comp Poly.nat_add (Poly.pair hf hg)
@[local fun_prop] private theorem mul {f g : I → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x*g x) := Poly.comp Poly.nat_mul (Poly.pair hf hg)
@[local fun_prop] private theorem div {f g : I → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x/g x) := Poly.comp (f := fun x : ℕ × ℕ => x.1/x.2) ⟨PolyProgram.natDiv⟩ (Poly.pair hf hg)
@[local fun_prop] private theorem modN {f g : I → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x%g x) := Poly.comp (f := fun x : ℕ × ℕ => x.1%x.2) ⟨PolyProgram.natMod⟩ (Poly.pair hf hg)
@[local fun_prop] private theorem bits {f : I → ℕ} (h : Poly f) :
    Poly (fun x => (f x).bits) := Poly.comp (f := Nat.bits) ⟨PolyProgram.natAsList⟩ h
@[local fun_prop] private theorem sizeP {f : I → ℕ} (h : Poly f) :
    Poly (fun x => (f x).size) := Poly.comp (f := Nat.size) ⟨PolyProgram.natSize⟩ h
@[local fun_prop] private theorem take {α : Type} [Coding α] [Inhabited α] {f : I → List α} {g : I → ℕ}
    (hf : Poly f) (hg : Poly g) : Poly (fun x => (f x).take (g x)) :=
  Poly.comp (f := fun p : List α × ℕ => p.1.take p.2) QMCNumericRuntime.parser_take_poly (Poly.pair hf hg)
@[local fun_prop] private theorem append {f g : I → List Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x++g x) := Poly.comp Poly.list_append (Poly.pair hf hg)
@[local fun_prop] private theorem widthP {f : I → ℕ} (h : Poly f) :
    Poly (fun x => width (f x)) := by unfold width;fun_prop
@[local fun_prop] private theorem radixP {f : I → ℕ} (h : Poly f) :
    Poly (fun x => radix (f x)) := by unfold radix;apply Poly.comp QMCNumericRuntime.bitValue_poly;fun_prop
@[local fun_prop] private theorem nP {f : I → ℕ} (h : Poly f) :
    Poly (fun x => nVal (f x)) := by unfold nVal;fun_prop
@[local fun_prop] private theorem graphP {f : I → ℕ} (h : Poly f) :
    Poly (fun x => graphWord (f x)) := by unfold graphWord;fun_prop
@[local fun_prop] private theorem trialP {f : I → ℕ} (h : Poly f) :
    Poly (fun x => trialWord (f x)) := by unfold trialWord;fun_prop
@[local fun_prop] private theorem vertsP {f : I → ℕ} (h : Poly f) :
    Poly (fun x => verts (f x)) := by
  unfold verts;apply take _ (nP h)
  exact Poly.comp (f := fun xs : List Bool => List.range xs.length) Poly.list_indices (bits h)
@[local fun_prop] private theorem matrixP {f : I → ℕ} (h : Poly f) :
    Poly (fun x => matrix (f x)) := by unfold matrix;fun_prop

def expected {n : ℕ} (adj : Fin n → Fin n → Bool) (r : ℕ) : List Bool :=
  if h : r < drawCount n then (candidateInput adj ((rankDraw n).symm ⟨r,h⟩)).getD [] else []

/-- Actual RAM code for serializing a trial. The three high registers hold n, the row-major
adjacency word, and the trial rank. The output word carries a sentinel even for a skipped call. -/
theorem prepare_exec :
    ∃ (floor : ℕ) (cmd : ℕ → Cmd) (room steps : Polynomial ℕ),
      ∀ (bank w n a r : ℕ) (adj : Fin n → Fin n → Bool) (τ : Tapes) (s : Store) (b : ℕ),
        floor ≤ bank → room.eval w ≤ b → s.Fits b → n≤w → n<2^w → a<2^w → r<2^w →
        (∀ u v : Fin n, a.testBit (v.val+n*u.val)=adj u v) →
        s.mem (cell bank)=n → s.mem (cell (bank+1))=a → s.mem (cell (bank+2))=r →
        s.mem (cell (bank+3))=2^w →
        ∃ t k, Exec τ (fun v => v.Fits b) (cmd bank) s t k ∧ k ≤ steps.eval b ∧
          t.mem 0=packed (expected adj r) ∧ t.out=s.out ∧
          ∀ i ≥ floor, t.mem (cell i)=s.mem (cell i) := by
  obtain ⟨prepare,fast,correct⟩ := prepare_cycle_parity_query_poly
  let emit := fun z => QMCNumericRuntime.bitValue (prepare (matrix z,trialWord z) ++ [true])
  have poly : Poly emit := by
    unfold emit;apply Poly.comp QMCNumericRuntime.bitValue_poly
    exact append (Poly.comp fast (Poly.pair (matrixP (h := Poly.identity)) (trialP (h := Poly.identity)))) (by fun_prop)
  obtain ⟨f,c,req,cost,run⟩ := StackMachine.fields_call emit poly 3 (by decide)
  refine ⟨f,c,req,cost,?_⟩
  intro bank w n a r adj τ s b high room fits nw hn ha hr graph N A R base
  have arg : ∀ i (hi : i<[n,a,r].length), s.mem (cell (bank+i))=[n,a,r][i] := by
    intro i hi
    have bound : i<3 := hi
    interval_cases i <;> simpa using (by first | exact N | exact A | exact R)
  obtain ⟨t,k,exec,le,out,rest⟩ := run bank w [n,a,r] rfl (by simpa using And.intro hn (And.intro ha hr)) τ s b
    high room fits base arg
  have ⟨_,_,rank,_⟩ := unpack w n a r hn ha hr
  rw [show emit (pack w [n,a,r]) = packed (expected adj r) by
    unfold emit;rw [sentinel,matrix_pack adj w a r nw hn ha hr graph,rank,correct];rfl] at out
  exact ⟨t,k,exec,le,out,rest⟩

end DirectedHamiltonicity.Main.CycleReduction.QueryRAM

open DirectedHamiltonicity.Main DirectedHamiltonicity.Main.CycleReduction
open TargetedSamplers TargetedSamplers.Structured Word BinaryStack

theorem solution :
    ∃ (floor : ℕ) (code : ℕ → Cmd) (room steps : Polynomial ℕ),
      ∀ (bank w n a r : ℕ) (adj : Fin n → Fin n → Bool) (τ : Tapes) (s : Store) (b : ℕ),
        floor ≤ bank → room.eval w ≤ b → s.Fits b → n ≤ w → n < 2^w → a < 2^w → r < 2^w →
        (∀ u v : Fin n, a.testBit (v.val+n*u.val) = adj u v) →
        s.mem (cell bank) = n → s.mem (cell (bank+1)) = a → s.mem (cell (bank+2)) = r →
        s.mem (cell (bank+3)) = 2^w →
        ∃ t k, Exec τ (fun v => v.Fits b) (code bank) s t k ∧ k ≤ steps.eval b ∧
          t.mem 0 = packed (if h : r < drawCount n then
            (candidateInput adj ((rankDraw n).symm ⟨r,h⟩)).getD [] else []) ∧
          t.out = s.out ∧ ∀ i ≥ floor, t.mem (cell i) = s.mem (cell i) := by
  exact QueryRAM.prepare_exec
