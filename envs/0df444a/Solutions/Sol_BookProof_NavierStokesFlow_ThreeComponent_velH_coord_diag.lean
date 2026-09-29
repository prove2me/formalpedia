-- Prove2me | solution 1 for BookProof.NavierStokesFlow.ThreeComponent.velH_coord_diag
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:55:13.995284+00:00
-- url     : https://prove2.me/submissions/1ef82493-09a1-4b4f-84d0-4de349740756

import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped ENNReal
namespace BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian
variable {ι : Type*}
namespace SignedHop
variable {sym : ι → ℝ} (S : SignedHop ι sym)
@[simp] theorem maj_shift : S.maj.shift = S.shift := rfl
@[simp] theorem hopH_coe (x : maxDom sym) (β : ι) :
    ((hopH S x : L2I ι) : ι → ℂ) β = S.hFun ((x : L2I ι) : ι → ℂ) β := rfl
end SignedHop
variable {sym : ι → ℝ}
@[simp] theorem listH_cons (S : SignedHop ι sym) (L : List (SignedHop ι sym)) :
    listH (S :: L) = SignedHop.hopH S + listH L := rfl
theorem SignedHop.hFun_single [DecidableEq ι] {sym : ι → ℝ} (S : SignedHop ι sym)
    {X : ι → ℂ} {o : ι} (hX : ∀ α, X α = if α = o then 1 else 0) (γ : ι) :
    S.hFun X γ = Complex.I * ((if γ = S.shift o then (S.amp o : ℂ) else 0)
      - (if S.shift γ = o then (S.amp γ : ℂ) else 0)) := by
  have h2 : (S.amp γ : ℂ) * X (S.shift γ)
      = if S.shift γ = o then (S.amp γ : ℂ) else 0 := by
    rw [hX]
    split <;> simp
  have h1 : S.maj.hop (fun α => (S.amp α : ℂ) * X α) γ
      = if γ = S.shift o then (S.amp o : ℂ) else 0 := by
    by_cases hb : ∃ α, S.shift α = γ
    · obtain ⟨α, rfl⟩ := hb
      have hiff : S.shift α = S.shift o ↔ α = o :=
        ⟨fun h => S.shift_injective h, fun h => by rw [h]⟩
      rw [show S.shift α = S.maj.shift α from rfl, ShiftData.hop_shift, hX]
      by_cases hao : α = o
      · subst hao; simp
      · rw [if_neg hao, mul_zero]
        exact (if_neg (fun h => hao (hiff.mp h))).symm
    · rw [ShiftData.hop_eq_zero _ _ (by simpa using hb)]
      exact (if_neg (fun h => hb ⟨o, h.symm⟩)).symm
  rw [SignedHop.hFun, h1, h2]
theorem listH_coe {sym : ι → ℝ} (L : List (SignedHop ι sym)) (x : maxDom sym) (γ : ι) :
    ((listH L x : L2I ι) : ι → ℂ) γ
      = (L.map (fun S => S.hFun ((x : L2I ι) : ι → ℂ) γ)).sum := by
  induction L with
  | nil => simp [listH]
  | cons S L ih =>
      rw [listH_cons]
      simp only [LinearMap.add_apply, lp.coeFn_add, Pi.add_apply, List.map_cons,
        List.sum_cons, SignedHop.hopH_coe, ih]
end BookProof.NavierStokesFlow.SignedShift

namespace BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
theorem velState_coe (β α : Vel) :
    ((velState A c β : L2I Vel) : Vel → ℂ) α = if α = β then 1 else 0 := by
  simp [velState, lp.single_apply, Pi.single_apply, eq_comm]

theorem norm_velState (β : Vel) : ‖(velState A c β : L2I Vel)‖ = 1 := by
  simp [velState]

/-- The coordinates of the coupled Hamiltonian on a Hermite basis vector: each
member of the family contributes its amplitude at the coordinate it hops to, and
minus its amplitude at the coordinate it hops from. -/
theorem velH_coe_single (β γ : Vel) :
    ((velH A c (velState A c β) : L2I Vel) : Vel → ℂ) γ
      = ((hopList A c).map (fun S => Complex.I *
          ((if γ = S.shift β then (S.amp β : ℂ) else 0)
            - (if S.shift γ = β then (S.amp γ : ℂ) else 0)))).sum := by
  rw [velH, SignedShift.listH_coe]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro S _
  exact S.hFun_single (velState_coe A c β) γ

/-- The family, written out. -/
theorem hopList_eq : hopList A c =
    [diagHop A c 0, shearHop A c 0,
      pairHop A c 0 0, rotHop A c 0 0, pairHop A c 0 1, rotHop A c 0 1,
      pairHop A c 0 2, rotHop A c 0 2,
     diagHop A c 1, shearHop A c 1,
      pairHop A c 1 0, rotHop A c 1 0, pairHop A c 1 1, rotHop A c 1 1,
      pairHop A c 1 2, rotHop A c 1 2,
     diagHop A c 2, shearHop A c 2,
      pairHop A c 2 0, rotHop A c 2 0, pairHop A c 2 1, rotHop A c 2 1,
      pairHop A c 2 2, rotHop A c 2 2] := rfl

@[simp] theorem diagHop_shift (i : Fin 3) : (diagHop A c i).shift = shDiag i := rfl
@[simp] theorem diagHop_amp (i : Fin 3) : (diagHop A c i).amp = ampDiag A i := rfl
@[simp] theorem shearHop_shift (i : Fin 3) : (shearHop A c i).shift = shShear i := rfl
@[simp] theorem shearHop_amp (i : Fin 3) : (shearHop A c i).amp = ampShear c i := rfl
@[simp] theorem pairHop_shift (i k : Fin 3) : (pairHop A c i k).shift = shPair i k := rfl
@[simp] theorem pairHop_amp (i k : Fin 3) : (pairHop A c i k).amp = ampPair A i k := rfl
@[simp] theorem rotHop_shift (i k : Fin 3) : (rotHop A c i k).shift = shRot i k := rfl
@[simp] theorem rotHop_amp (i k : Fin 3) : (rotHop A c i k).amp = ampRot A i k := rfl

set_option maxHeartbeats 1000000 in
-- the twenty-four members of the family are expanded and evaluated one by one
/-- **The strain coupling of two distinct components.**  The matrix entry of `H`
between the ground state and the doubly excited state `e₁ + e₂` is the symmetric
part `(A₁₂ + A₂₁)/2` of the velocity gradient: the two components really are
coupled. -/
theorem velH_coord_pair :
    ((velH A c (velState A c ![0, 0, 0]) : L2I Vel) : Vel → ℂ) ![1, 1, 0]
      = Complex.I * (((A 0 1 + A 1 0) / 2 : ℝ) : ℂ) := by
  rw [velH_coe_single, hopList_eq]
  simp +decide [ampPair, coefPair]
  ring

set_option maxHeartbeats 1000000 in
-- the twenty-four members of the family are expanded and evaluated one by one
/-- **The vorticity coupling of two distinct components.**  The matrix entry of
`H` between the state `e₂` and the state `e₁` is the antisymmetric part
`(A₁₂ − A₂₁)/2` of the velocity gradient: the number-conserving hopping, the one
whose amplitude is not monotone, really is present. -/
theorem velH_coord_rot :
    ((velH A c (velState A c ![0, 1, 0]) : L2I Vel) : Vel → ℂ) ![1, 0, 0]
      = Complex.I * (((A 0 1 - A 1 0) / 2 : ℝ) : ℂ) := by
  rw [velH_coe_single, hopList_eq]
  simp +decide [ampRot, coefRot]
  ring

set_option maxHeartbeats 1000000 in
-- the twenty-four members of the family are expanded and evaluated one by one
/-- The matrix entry carried by the constant part `c₁` of the first fiber field:
the `±1`-hopping out of the ground state. -/
theorem velH_coord_shear :
    ((velH A c (velState A c ![0, 0, 0]) : L2I Vel) : Vel → ℂ) ![1, 0, 0]
      = Complex.I * ((c 0 / Real.sqrt 2 : ℝ) : ℂ) := by
  rw [velH_coe_single, hopList_eq]
  simp +decide [ampShear]

set_option maxHeartbeats 1000000 in
-- the twenty-four members of the family are expanded and evaluated one by one
/-- The matrix entry carried by the diagonal (self-advection) rate `A₁₁`: the
`±2`-hopping out of the ground state. -/
theorem velH_coord_diag :
    ((velH A c (velState A c ![0, 0, 0]) : L2I Vel) : Vel → ℂ) ![2, 0, 0]
      = Complex.I * ((A 0 0 * Real.sqrt 2 / 2 : ℝ) : ℂ) := by
  rw [velH_coe_single, hopList_eq]
  simp +decide [ampDiag, ampPair, coefPair]
  ring

/-- With a non-zero symmetric part the two components are genuinely coupled. -/
theorem velH_ne_zero_of_strain (h : A 0 1 + A 1 0 ≠ 0) :
    velH A c (velState A c ![0, 0, 0]) ≠ 0 := by
  intro h0
  have hco := velH_coord_pair A c
  rw [h0] at hco
  simp only [lp.coeFn_zero, Pi.zero_apply] at hco
  have : ((A 0 1 + A 1 0) / 2 : ℝ) = 0 := by
    have h1 : (((A 0 1 + A 1 0) / 2 : ℝ) : ℂ) = 0 := by
      have := hco.symm
      simpa [Complex.ext_iff] using this
    exact_mod_cast h1
  exact h (by linarith)

/-- With a non-zero antisymmetric part the vorticity coupling is genuinely
present. -/
theorem velH_ne_zero_of_vorticity (h : A 0 1 - A 1 0 ≠ 0) :
    velH A c (velState A c ![0, 1, 0]) ≠ 0 := by
  intro h0
  have hco := velH_coord_rot A c
  rw [h0] at hco
  simp only [lp.coeFn_zero, Pi.zero_apply] at hco
  have : ((A 0 1 - A 1 0) / 2 : ℝ) = 0 := by
    have h1 : (((A 0 1 - A 1 0) / 2 : ℝ) : ℂ) = 0 := by
      have := hco.symm
      simpa [Complex.ext_iff] using this
    exact_mod_cast h1
  exact h (by linarith)

/-! ## Unboundedness -/

theorem vel_eq_iff (x y : Vel) : x = y ↔ x 0 = y 0 ∧ x 1 = y 1 ∧ x 2 = y 2 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2⟩
    funext j
    fin_cases j <;> assumption

theorem raise_apply (i : Fin 3) (β : Vel) (j : Fin 3) :
    raise i β j = β j + (if j = i then 1 else 0) := by
  by_cases h : j = i
  · subst h; simp [raise]
  · simp [raise_of_ne h, h]

theorem shDiag_apply (i : Fin 3) (β : Vel) (j : Fin 3) :
    shDiag i β j = β j + (if j = i then 2 else 0) := by
  by_cases h : j = i
  · subst h; simp [shDiag, raise]
  · simp [shDiag, raise_of_ne h, h]

theorem shPair_apply (i k : Fin 3) (β : Vel) (j : Fin 3) :
    shPair i k β j = β j + (if j = k then 1 else 0) + (if j = i then 1 else 0) := by
  rw [shPair, raise_apply, raise_apply]

theorem shShear_apply (i : Fin 3) (β : Vel) (j : Fin 3) :
    shShear i β j = β j + (if j = i then 1 else 0) := raise_apply i β j

set_option maxHeartbeats 1000000 in
-- the twenty-four members of the family are expanded and evaluated one by one
/-- The `±2`-hopping entry of the first component along the whole tower of
excited states: its amplitude grows like the Hermite level. -/
theorem velH_coord_diag_tower (n : ℕ) :
    ((velH A c (velState A c ![n + 1, 0, 0]) : L2I Vel) : Vel → ℂ) ![n + 3, 0, 0]
      = Complex.I * ((A 0 0 / 2 * Real.sqrt (((n : ℝ) + 1 + 1) * ((n : ℝ) + 1 + 2)) : ℝ) : ℂ) := by
  have hne : ¬ (n + 3 + 1 = n) := by omega
  rw [velH_coe_single, hopList_eq]
  simp [vel_eq_iff, shDiag_apply, shPair_apply, shShear_apply, shRot, swapVel, lower,
    raise_apply, Equiv.swap_apply_def, hne, ampDiag, ampPair, coefPair]

/-- **The coupled Hamiltonian is unbounded**: essential self-adjointness above
is not a boundedness phenomenon. -/
theorem velH_not_bounded (hA : A 0 0 ≠ 0) (C : ℝ) :
    ∃ β : Vel, ‖(velState A c β : L2I Vel)‖ = 1
      ∧ C < ‖(velH A c (velState A c β) : L2I Vel)‖ := by
  have hpos : 0 < |A 0 0| := abs_pos.mpr hA
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * (|C| + 1) / |A 0 0|)
  refine ⟨![n + 1, 0, 0], norm_velState A c _, ?_⟩
  have hb : ‖((velH A c (velState A c ![n + 1, 0, 0]) : L2I Vel) : Vel → ℂ) ![n + 3, 0, 0]‖
      ≤ ‖(velH A c (velState A c ![n + 1, 0, 0]) : L2I Vel)‖ :=
    lp.norm_apply_le_norm (by norm_num) _ _
  rw [velH_coord_diag_tower] at hb
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsq : ((n : ℝ) + 2) ≤ Real.sqrt (((n : ℝ) + 1 + 1) * ((n : ℝ) + 1 + 2)) := by
    have h := Real.sqrt_le_sqrt
      (show ((n : ℝ) + 2) ^ 2 ≤ ((n : ℝ) + 1 + 1) * ((n : ℝ) + 1 + 2) by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at h
  have hnorm : ‖Complex.I * ((A 0 0 / 2 * Real.sqrt (((n : ℝ) + 1 + 1) * ((n : ℝ) + 1 + 2)) :
        ℝ) : ℂ)‖
      = |A 0 0| / 2 * Real.sqrt (((n : ℝ) + 1 + 1) * ((n : ℝ) + 1 + 2)) := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    norm_num
  rw [hnorm] at hb
  have hmul : 2 * (|C| + 1) < |A 0 0| * (n : ℝ) := by
    rw [div_lt_iff₀ hpos] at hn
    linarith
  have hC : C ≤ |C| := le_abs_self C
  nlinarith [hsq, hpos.le]

/-- The finite-mode core is dense, so the coupled Hamiltonian is a densely
defined operator and its essential self-adjointness is the statement it should
be. -/
theorem velH_domain_dense :
    Dense ((lpFiniteModes Vel : Submodule ℂ (L2I Vel)) : Set (L2I Vel)) :=
  lpFiniteModes_dense
end BookProof.NavierStokesFlow.ThreeComponent

open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
open scoped ENNReal
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem solution :
    ((velH A c (velState A c ![0, 0, 0]) : L2I Vel) : Vel → ℂ) ![2, 0, 0]
      = Complex.I * ((A 0 0 * Real.sqrt 2 / 2 : ℝ) : ℂ) := by
  exact BookProof.NavierStokesFlow.ThreeComponent.velH_coord_diag A c

#print axioms solution
