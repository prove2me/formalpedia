-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_ringHom_centralizer_standard_existsUnique_eq_add_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c2267205-0235-59d2-8b1f-583b845fab5c

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_LubinTateModule
import Definitions.Def_CerednikDrinfeld_StandardFormalODModule
import Theorems.Thm_MvFormalGroup_End_injective_and_forall_exists_eq_of_forall_commute_of_toPowerSeries_eq_X_pow_card
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_ringHom_centralizer_standard_existsUnique_eq_add_mul

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

noncomputable section

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.LubinTate CerednikDrinfeld.Standard

namespace P2mKcStdEnd

variable {p : ℕ} [Fact p.Prime] {k : Type u} [Field k] [CharP k p] (j : Zp2 p →+* k)

local notation "𝕆" => Zp2 p
local notation "σ" => (WittVector.frobenius : Zp2 p →+* Zp2 p)

abbrev EF : Type u := MvFormalGroup.End (modB j).F

abbrev ES : Type u := MvFormalGroup.End (sigmaBar j)

def Mx (x : Fin 2 → Fin 2 → ES j) : EF j :=
  cell j 0 0 (x 0 0) + cell j 0 1 (x 0 1) + (cell j 1 0 (x 1 0) + cell j 1 1 (x 1 1))

theorem eq_Mx (E : EF j) : E = Mx j fun i i' => entry j i i' E := eq_sum_cell_entry j E

theorem entry_Mx (x : Fin 2 → Fin 2 → ES j) (i i' : Fin 2) : entry j i i' (Mx j x) = x i i' := by
  rw [Mx, entry_add, entry_add, entry_add, entry_cell, entry_cell, entry_cell, entry_cell]
  revert i i'
  simp only [Fin.forall_fin_two, Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one, add_zero, zero_add,
    and_self]

theorem Mx_inj {x y : Fin 2 → Fin 2 → ES j} (h : Mx j x = Mx j y) : x = y := by
  funext i i'
  rw [← entry_Mx j x i i', ← entry_Mx j y i i', h]

theorem Mx_add (x y : Fin 2 → Fin 2 → ES j) : Mx j x + Mx j y = Mx j fun i i' => x i i' + y i i' := by
  simp only [Mx, cell_add]
  abel

def mxMul (x y : Fin 2 → Fin 2 → ES j) : Fin 2 → Fin 2 → ES j :=
  fun i i' => x i 0 * y 0 i' + x i 1 * y 1 i'

theorem Mx_mul (x y : Fin 2 → Fin 2 → ES j) : Mx j x * Mx j y = Mx j (mxMul j x y) := by
  simp only [Mx, mxMul, add_mul, mul_add, cell_mul_cell, Fin.isValue, ↓reduceIte, one_ne_zero,
    zero_ne_one, add_zero, zero_add, cell_add]
  abel

theorem Mx_one : Mx j (fun i i' => if i = i' then 1 else 0) = 1 := by
  rw [one_eq_cell_add_cell, Mx]
  simp only [Fin.isValue, ↓reduceIte, zero_ne_one, one_ne_zero, cell_zero, add_zero, zero_add]

def diag (x y : ES j) : Fin 2 → Fin 2 → ES j := fun i i' => if i = i' then (if i = 0 then x else y) else 0

def anti (x y : ES j) : Fin 2 → Fin 2 → ES j := fun i i' => if i = i' then 0 else (if i = 0 then x else y)

theorem Mx_diag (x y : ES j) : Mx j (diag j x y) = cell j 0 0 x + cell j 1 1 y := by
  simp only [Mx, diag, Fin.isValue, ↓reduceIte, zero_ne_one, one_ne_zero, cell_zero, add_zero, zero_add]

theorem Mx_anti (x y : ES j) : Mx j (anti j x y) = cell j 0 1 x + cell j 1 0 y := by
  simp only [Mx, anti, Fin.isValue, ↓reduceIte, zero_ne_one, one_ne_zero, cell_zero, add_zero, zero_add]

theorem actEnd_eq_Mx (a : 𝕆) : (modB j).actEnd a = Mx j (diag j (rho j a) (rho j (σ a))) := by
  rw [Mx_diag, actEnd_eq]

theorem varpiEnd_eq_Mx : (modB j).varpiEnd = Mx j (anti j (rho j (p : 𝕆)) 1) := by
  rw [Mx_anti, varpiEnd_eq]

theorem mxMul_diag_left (x y : ES j) (m : Fin 2 → Fin 2 → ES j) :
    mxMul j (diag j x y) m = fun i i' => (if i = 0 then x else y) * m i i' := by
  funext i i'
  revert i i'
  simp only [Fin.forall_fin_two, mxMul, diag, Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one, zero_mul,
    add_zero, zero_add, and_self]

theorem mxMul_diag_right (x y : ES j) (m : Fin 2 → Fin 2 → ES j) :
    mxMul j m (diag j x y) = fun i i' => m i i' * (if i' = 0 then x else y) := by
  funext i i'
  revert i i'
  simp only [Fin.forall_fin_two, mxMul, diag, Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one, mul_zero,
    add_zero, zero_add, and_self]

theorem mxMul_anti_left (x y : ES j) (m : Fin 2 → Fin 2 → ES j) :
    mxMul j (anti j x y) m = fun i i' => if i = 0 then x * m 1 i' else y * m 0 i' := by
  funext i i'
  revert i i'
  simp only [Fin.forall_fin_two, mxMul, anti, Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one, zero_mul,
    add_zero, zero_add, and_self]

theorem mxMul_anti_right (x y : ES j) (m : Fin 2 → Fin 2 → ES j) :
    mxMul j m (anti j x y) = fun i i' => if i' = 0 then m i 1 * y else m i 0 * x := by
  funext i i'
  revert i i'
  simp only [Fin.forall_fin_two, mxMul, anti, Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one, mul_zero,
    add_zero, zero_add, and_self]

abbrev genSet : Set (EF j) := Set.range (modB j).actEnd ∪ {(modB j).varpiEnd}

abbrev S : Subring (EF j) := Subring.centralizer (genSet j)

theorem mem_S_iff (E : EF j) :
    E ∈ S j ↔ (∀ a, (modB j).actEnd a * E = E * (modB j).actEnd a) ∧
      (modB j).varpiEnd * E = E * (modB j).varpiEnd := by
  rw [Subring.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨fun a => h _ (Or.inl ⟨a, rfl⟩), h _ (Or.inr rfl)⟩
  · rintro ⟨h1, h2⟩ g hg
    rcases hg with ⟨a, rfl⟩ | hg
    · exact h1 a
    · rw [Set.mem_singleton_iff] at hg; rw [hg]; exact h2

theorem hp0 : (p : ℕ) ≠ 0 := (Fact.out : p.Prime).ne_zero

theorem card_two : Fintype.card (GaloisField p 2) = p ^ 2 := card_GF

theorem oneDim :
    Function.Injective (rho j) ∧ ∀ e : ES j, (∀ a, e * rho j a = rho j a * e) → ∃ a, e = rho j a :=
  MvFormalGroup.End.injective_and_forall_exists_eq_of_forall_commute_of_toPowerSeries_eq_X_pow_card p j
    (sigmaBar j) (rho j) (coeff_single_rho j) (by rw [rho_p_toPowerSeries, card_two])

def D (e : ES j) : k := coeff (Finsupp.single 0 1) (e.toPowerSeries 0)

theorem D_mul (e e' : ES j) : D j (e * e') = D j e * D j e' := by
  show coeff _ (subst e'.toPowerSeries (e.toPowerSeries 0)) = _
  rw [MvFormalGroup.coeff_single_subst e'.constantCoeff_eq_zero]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton]
  rfl

theorem D_rho (a : 𝕆) : D j (rho j a) = j a := coeff_single_rho j a

theorem D_phi : D j (phi j) = 0 := by
  show coeff (Finsupp.single 0 1) ((X 0 : MvPowerSeries (Fin 1) k) ^ p) = 0
  rw [coeff_X_pow, if_neg]
  intro h
  have := congrArg (fun d => d 0) h
  simp only [Finsupp.single_eq_same] at this
  exact (Fact.out : p.Prime).one_lt.ne this

theorem j_eq_zero_iff (c : 𝕆) : j c = 0 ↔ c.coeff 0 = 0 := by
  constructor
  · intro hc
    by_contra h0
    exact ((WittVector.isUnit_of_coeff_zero_ne_zero c h0).map j).ne_zero hc
  · intro h0
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp
      ((WittVector.mem_span_p_iff_coeff_zero_eq_zero c).mpr h0)
    rw [← hd, map_mul, map_natCast, CharP.cast_eq_zero, mul_zero]

theorem exists_eq_p_mul_of_j_eq_zero {c : 𝕆} (hc : j c = 0) : ∃ c', c = (p : 𝕆) * c' := by
  have h := (WittVector.mem_span_p_iff_coeff_zero_eq_zero c).mpr ((j_eq_zero_iff j c).mp hc)
  exact Ideal.mem_span_singleton.mp h

theorem mul_phi_cancel {x y : ES j} (h : x * phi j = y * phi j) : x = y := by
  have hser : ∀ z : ES j, (z * phi j).toPowerSeries 0 = expand p hp0 (z.toPowerSeries 0) := by
    intro z
    rw [MvFormalGroup.End.toPowerSeries_mul, expand, coe_substAlgHom]
    show subst (phi j).toPowerSeries (z.toPowerSeries 0) = _
    congr 1
    funext s
    rw [phi_toPowerSeries, Fin.fin_one_eq_zero s]
  have h0 : x.toPowerSeries 0 = y.toPowerSeries 0 := by
    have := congrArg (fun z : ES j => z.toPowerSeries 0) h
    simp only [hser] at this
    ext m
    have := congrArg (coeff (p • m)) this
    rwa [coeff_expand_smul, coeff_expand_smul] at this
  apply MvFormalGroup.Hom.ext
  funext l
  rw [Fin.fin_one_eq_zero l, h0]

theorem frobenius_frobenius' (a : 𝕆) : σ (σ a) = a := LubinTate.frobenius_frobenius a

theorem phi_mul_rho' (a : 𝕆) : phi j * rho j a = rho j (σ a) * phi j := phi_mul_rho j a

theorem rho_phi_comm_p : rho j (p : 𝕆) * phi j = phi j * rho j (p : 𝕆) := by
  rw [← phi_mul_phi, mul_assoc]

theorem mx_ext {x y : Fin 2 → Fin 2 → ES j} (h00 : x 0 0 = y 0 0) (h01 : x 0 1 = y 0 1)
    (h10 : x 1 0 = y 1 0) (h11 : x 1 1 = y 1 1) : x = y := by
  funext i i'
  revert i i'
  rw [Fin.forall_fin_two, Fin.forall_fin_two, Fin.forall_fin_two]
  exact ⟨⟨h00, h01⟩, h10, h11⟩

structure Entries (E : EF j) : Prop where
  e00 : ∀ a, rho j a * entry j 0 0 E = entry j 0 0 E * rho j a
  e10 : ∀ a, rho j (σ a) * entry j 1 0 E = entry j 1 0 E * rho j a
  e11 : entry j 1 1 E = entry j 0 0 E
  e01 : entry j 0 1 E = rho j (p : 𝕆) * entry j 1 0 E

theorem entries_of_mem {E : EF j} (hE : E ∈ S j) : Entries j E := by
  rw [mem_S_iff] at hE
  obtain ⟨hact, hvarpi⟩ := hE
  set m : Fin 2 → Fin 2 → ES j := fun i i' => entry j i i' E with hm
  have hEm : E = Mx j m := eq_Mx j E
  have hA : ∀ a, mxMul j (diag j (rho j a) (rho j (σ a))) m = mxMul j m (diag j (rho j a) (rho j (σ a))) := by
    intro a
    apply Mx_inj j
    rw [← Mx_mul, ← Mx_mul, ← actEnd_eq_Mx, ← hEm, hact a]
  have hV : mxMul j (anti j (rho j (p : 𝕆)) 1) m = mxMul j m (anti j (rho j (p : 𝕆)) 1) := by
    apply Mx_inj j
    rw [← Mx_mul, ← Mx_mul, ← varpiEnd_eq_Mx, ← hEm, hvarpi]
  simp only [mxMul_diag_left, mxMul_diag_right] at hA
  rw [mxMul_anti_left, mxMul_anti_right] at hV
  refine ⟨fun a => ?_, fun a => ?_, ?_, ?_⟩
  · have := congrFun (congrFun (hA a) 0) 0
    simpa using this
  · have := congrFun (congrFun (hA a) 1) 0
    simpa using this
  · have := congrFun (congrFun hV 1) 0
    simpa using this.symm
  · have := congrFun (congrFun hV 0) 0
    simpa using this.symm

def A₀ (a : 𝕆) : EF j := Mx j (diag j (rho j a) (rho j a))

def Ψ₀ : EF j := Mx j (anti j (rho j (p : 𝕆) * phi j) (phi j))

theorem A₀_mem (a : 𝕆) : A₀ j a ∈ S j := by
  rw [mem_S_iff]
  constructor
  · intro b
    rw [actEnd_eq_Mx, A₀, Mx_mul, Mx_mul, mxMul_diag_left, mxMul_diag_right]
    refine congrArg (Mx j) (mx_ext j ?_ ?_ ?_ ?_) <;>
      simp only [diag, Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one, mul_zero, zero_mul, rho_mul_comm j]
  · rw [varpiEnd_eq_Mx, A₀, Mx_mul, Mx_mul, mxMul_anti_left, mxMul_anti_right]
    refine congrArg (Mx j) (mx_ext j ?_ ?_ ?_ ?_) <;>
      simp only [diag, Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one, mul_zero, zero_mul, mul_one,
        one_mul, rho_mul_comm j]

theorem Ψ₀_mem : Ψ₀ j ∈ S j := by
  rw [mem_S_iff]
  constructor
  · intro b
    rw [actEnd_eq_Mx, Ψ₀, Mx_mul, Mx_mul, mxMul_diag_left, mxMul_diag_right]
    refine congrArg (Mx j) (mx_ext j ?_ ?_ ?_ ?_) <;>
      simp only [anti, Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one, mul_zero, zero_mul]
    · rw [mul_assoc, phi_mul_rho', frobenius_frobenius', ← mul_assoc, ← mul_assoc, rho_mul_comm j]
    · rw [phi_mul_rho']
  · rw [varpiEnd_eq_Mx, Ψ₀, Mx_mul, Mx_mul, mxMul_anti_left, mxMul_anti_right]
    refine congrArg (Mx j) (mx_ext j ?_ ?_ ?_ ?_) <;>
      simp only [anti, Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one, mul_zero, zero_mul, mul_one, one_mul]
    exact rho_phi_comm_p j

def A : 𝕆 →+* S j where
  toFun a := ⟨A₀ j a, A₀_mem j a⟩
  map_one' := by
    apply Subtype.ext
    show A₀ j 1 = 1
    rw [A₀, map_one, ← Mx_one]
    refine congrArg (Mx j) (mx_ext j ?_ ?_ ?_ ?_) <;>
      simp only [diag, Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one]
  map_mul' a b := by
    apply Subtype.ext
    show A₀ j (a * b) = A₀ j a * A₀ j b
    rw [A₀, A₀, A₀, Mx_mul, mxMul_diag_left, map_mul]
    refine congrArg (Mx j) (mx_ext j ?_ ?_ ?_ ?_) <;>
      simp only [diag, Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one, mul_zero]
  map_zero' := by
    apply Subtype.ext
    show A₀ j 0 = 0
    rw [A₀, map_zero, Mx_diag, cell_zero, cell_zero, add_zero]
  map_add' a b := by
    apply Subtype.ext
    show A₀ j (a + b) = A₀ j a + A₀ j b
    rw [A₀, A₀, A₀, Mx_add, map_add]
    refine congrArg (Mx j) (mx_ext j ?_ ?_ ?_ ?_) <;>
      simp only [diag, Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one, add_zero]

theorem A_val (a : 𝕆) : (A j a : EF j) = A₀ j a := rfl

def Ψ : S j := ⟨Ψ₀ j, Ψ₀_mem j⟩

theorem Ψ_val : (Ψ j : EF j) = Ψ₀ j := rfl

theorem Ψ_mul_Ψ : Ψ j * Ψ j = A j ((p : 𝕆) ^ 2) := by
  apply Subtype.ext
  show Ψ₀ j * Ψ₀ j = A₀ j ((p : 𝕆) ^ 2)
  rw [Ψ₀, A₀, Mx_mul, mxMul_anti_left]
  have h4 : phi j * (rho j (p : 𝕆) * phi j) = rho j ((p : 𝕆) ^ 2) := by
    rw [sq, map_mul, ← phi_mul_phi]
    simp only [mul_assoc]
  have h4' : rho j (p : 𝕆) * phi j * phi j = rho j ((p : 𝕆) ^ 2) := by
    rw [mul_assoc, phi_mul_phi, ← map_mul, sq]
  refine congrArg (Mx j) (mx_ext j ?_ ?_ ?_ ?_) <;>
    simp only [anti, diag, Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one, mul_zero, h4, h4']

theorem Ψ_mul_A (a : 𝕆) : Ψ j * A j a = A j (σ a) * Ψ j := by
  apply Subtype.ext
  show Ψ₀ j * A₀ j a = A₀ j (σ a) * Ψ₀ j
  rw [Ψ₀, A₀, A₀, Mx_mul, Mx_mul, mxMul_anti_left, mxMul_anti_right]
  refine congrArg (Mx j) (mx_ext j ?_ ?_ ?_ ?_) <;>
    simp only [diag, Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one, mul_zero, zero_mul]
  · rw [mul_assoc, phi_mul_rho', ← mul_assoc, ← mul_assoc, rho_mul_comm j]
  · rw [phi_mul_rho']

def coordMx (a c : 𝕆) : Fin 2 → Fin 2 → ES j :=
  fun i i' => if i = i' then rho j a else (if i = 0 then rho j c * (rho j (p : 𝕆) * phi j) else rho j c * phi j)

theorem A_add_A_mul_Ψ_val (a c : 𝕆) : ((A j a + A j c * Ψ j : S j) : EF j) = Mx j (coordMx j a c) := by
  show A₀ j a + A₀ j c * Ψ₀ j = _
  rw [A₀, A₀, Ψ₀, Mx_mul, Mx_add, mxMul_diag_left]
  refine congrArg (Mx j) (mx_ext j ?_ ?_ ?_ ?_) <;>
    simp only [anti, diag, coordMx, Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one, mul_zero, add_zero,
      zero_add]

theorem exists_coords {E : EF j} (hE : E ∈ S j) : ∃ a c : 𝕆, E = ((A j a + A j c * Ψ j : S j) : EF j) := by
  have hEn := entries_of_mem j hE

  obtain ⟨a, ha⟩ := (oneDim j).2 (entry j 0 0 E) fun b => (hEn.e00 b).symm

  set g : ES j := entry j 1 0 E * phi j with hg
  have hgC : ∀ b, g * rho j b = rho j b * g := by
    intro b
    rw [hg, mul_assoc, phi_mul_rho', ← mul_assoc, ← hEn.e10 (σ b), frobenius_frobenius', mul_assoc]
  obtain ⟨g', hg'⟩ := (oneDim j).2 g hgC
  have hDg : j g' = 0 := by
    rw [← D_rho j, ← hg', hg, D_mul, D_phi, mul_zero]
  obtain ⟨c, hc⟩ := exists_eq_p_mul_of_j_eq_zero j hDg
  have h10 : entry j 1 0 E = rho j c * phi j := by
    apply mul_phi_cancel j
    rw [← hg, hg', hc, mul_assoc, phi_mul_phi, ← map_mul, mul_comm c]
  refine ⟨a, c, ?_⟩
  rw [A_add_A_mul_Ψ_val, eq_Mx j E]
  refine congrArg (Mx j) (mx_ext j ?_ ?_ ?_ ?_) <;>
    simp only [coordMx, Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one]
  · exact ha
  · rw [hEn.e01, h10, ← mul_assoc, ← mul_assoc, rho_mul_comm j]
  · exact h10
  · rw [hEn.e11, ha]

theorem coords_unique {a c a' c' : 𝕆} (h : (A j a + A j c * Ψ j : S j) = A j a' + A j c' * Ψ j) :
    a = a' ∧ c = c' := by
  have h' := congrArg (fun z : S j => (z : EF j)) h
  simp only [A_add_A_mul_Ψ_val] at h'
  have h'' := Mx_inj j h'
  have h00 := congrFun (congrFun h'' 0) 0
  have h10 := congrFun (congrFun h'' 1) 0
  simp only [coordMx, Fin.isValue, ↓reduceIte, one_ne_zero] at h00 h10
  exact ⟨(oneDim j).1 h00, (oneDim j).1 (mul_phi_cancel j h10)⟩

theorem existsUnique_coords (e : S j) : ∃! ac : 𝕆 × 𝕆, e = A j ac.1 + A j ac.2 * Ψ j := by
  obtain ⟨a, c, h⟩ := exists_coords j e.2
  refine ⟨⟨a, c⟩, Subtype.ext h, ?_⟩
  rintro ⟨a', c'⟩ h'
  have := coords_unique j ((Subtype.ext h).symm.trans h')
  rw [this.1, this.2]

end P2mKcStdEnd

end

open P2mKcStdEnd CerednikDrinfeld in

theorem solution
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] (j : Zp2 p →+* k) :
    ∃ (A : Zp2 p →+*
          Subring.centralizer
            (Set.range (SpecialFormalODModule.standard j).toFormalODModule.actEnd ∪
              {(SpecialFormalODModule.standard j).toFormalODModule.varpiEnd}))
      (Ψ : Subring.centralizer
            (Set.range (SpecialFormalODModule.standard j).toFormalODModule.actEnd ∪
              {(SpecialFormalODModule.standard j).toFormalODModule.varpiEnd})),
      (∀ a, (A a : MvFormalGroup.End (SpecialFormalODModule.standard j).F) =
          Standard.cell j 0 0 (LubinTate.rho j a) + Standard.cell j 1 1 (LubinTate.rho j a)) ∧
      (Ψ : MvFormalGroup.End (SpecialFormalODModule.standard j).F) =
          Standard.cell j 0 1 (LubinTate.rho j (p : Zp2 p) * LubinTate.phi j) +
            Standard.cell j 1 0 (LubinTate.phi j) ∧
      Ψ * Ψ = A ((p : Zp2 p) ^ 2) ∧
      (∀ a, Ψ * A a = A (WittVector.frobenius a) * Ψ) ∧
      ∀ e, ∃! ac : Zp2 p × Zp2 p, e = A ac.1 + A ac.2 * Ψ :=
  ⟨P2mKcStdEnd.A j, P2mKcStdEnd.Ψ j, fun a => Mx_diag j _ _, Mx_anti j _ _, Ψ_mul_Ψ j, Ψ_mul_A j,
    existsUnique_coords j⟩

end S_CerednikDrinfeld_SpecialFormalODModule_exists_ringHom_centralizer_standard_existsUnique_eq_add_mul
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_ringHom_centralizer_standard_existsUnique_eq_add_mul (solution)
