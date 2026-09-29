-- Prove2me | solution 1 for ClassicalSchur.coveredBySumFree_liftSeq
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-26T21:37:12.796881+00:00
-- url     : https://prove2.me/submissions/eefe6db2-afa4-4ab7-b5f2-eed91f7c516f

-- Generated from lean/ClassicalSchur/Lift.lean
--   imports : 2 platform node(s), 2 definition bundle(s)
--   inlined : 2 file-scoped / sub-threshold helper(s)
--   rename  : coveredBySumFree_liftSeq -> solution, hoisted out of the namespace
import Definitions.Def_ClassicalSchurBasic
import Definitions.Def_ClassicalSchurLift
import Theorems.Thm_ClassicalSchur_liftPrefix_strictMono
import Theorems.Thm_ClassicalSchur_liftSeq_take_sum
import Mathlib



namespace ClassicalSchur

/-- Every block sum is a difference of two prefix sums (ER Proposition 2.7,
the other direction). -/
theorem exists_of_mem_blockSums {A : List ℕ} {s : ℕ} (hs : s ∈ blockSums A) :
    ∃ i j, i < j ∧ j ≤ A.length ∧ s = (A.take j).sum - (A.take i).sum := by
  obtain ⟨B, ⟨u, v, rfl⟩, hne, rfl⟩ := hs
  have hB : 0 < B.length := List.length_pos_iff.mpr hne
  refine ⟨u.length, u.length + B.length, by omega, by simp only [List.length_append]; omega, ?_⟩
  have h1 : (u ++ B ++ v).take (u.length + B.length) = u ++ B := by
    rw [show u.length + B.length = (u ++ B).length by simp, List.take_left]
  have h2 : (u ++ B ++ v).take u.length = u := by
    rw [List.append_assoc, List.take_left]
  rw [h1, h2, List.sum_append]
  omega

@[simp] theorem liftSeq_length (m₁ m₂ M : ℕ) : (liftSeq m₁ m₂ M).length = m₁ * m₂ - 1 := by
  simp [liftSeq]

end ClassicalSchur

open ClassicalSchur in
theorem solution {m₁ m₂ q M : ℕ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hM : 3 * m₁ - 2 ≤ M) (C : Fin q → Set (ZMod m₁ × ZMod m₂))
    (hC : ∀ i, GroupSumFree (C i)) (hcov : ∀ g : ZMod m₁ × ZMod m₂, g ≠ 0 → ∃ i, g ∈ C i) :
    CoveredBySumFree (blockSums (liftSeq m₁ m₂ M)) q := by
  classical
  have hM' : m₁ ≤ M := by omega
  -- Each block sum `d` has a form `d = r + M e` with `|r| < m₁`, `0 ≤ e < m₂`,
  -- and `r > 0` when `e = 0`.
  have hrep : ∀ d : ℕ, ∃ re : ℤ × ℤ, d ∈ blockSums (liftSeq m₁ m₂ M) →
      (d : ℤ) = re.1 + M * re.2 ∧ -(m₁ : ℤ) < re.1 ∧ re.1 < m₁ ∧ 0 ≤ re.2 ∧ re.2 < m₂ ∧
        (re.2 = 0 → 0 < re.1) := by
    intro d
    by_cases hd : d ∈ blockSums (liftSeq m₁ m₂ M)
    swap
    · exact ⟨(0, 0), fun h => absurd h hd⟩
    obtain ⟨a, b, hab, hb, rfl⟩ := exists_of_mem_blockSums hd
    rw [liftSeq_length] at hb
    rw [liftSeq_take_sum hm₁ hM' hb, liftSeq_take_sum hm₁ hM' (by omega)]
    have hpab := liftPrefix_strictMono hm₁ hM' hab
    refine ⟨(((b % m₁ : ℕ) : ℤ) - ((a % m₁ : ℕ) : ℤ), ((b / m₁ : ℕ) : ℤ) - ((a / m₁ : ℕ) : ℤ)),
      fun _ => ?_⟩
    have hja : a / m₁ ≤ b / m₁ := Nat.div_le_div_right hab.le
    have hjb : b / m₁ < m₂ := (Nat.div_lt_iff_lt_mul hm₁).2 (by
      have : 0 < m₁ * m₂ := Nat.mul_pos hm₁ hm₂
      rw [Nat.mul_comm]; omega)
    have hua := Nat.mod_lt a hm₁
    have hub := Nat.mod_lt b hm₁
    have hda := Nat.mod_add_div a m₁
    have hdb := Nat.mod_add_div b m₁
    unfold liftPrefix at hpab ⊢
    generalize a % m₁ = ua at hua hda hpab ⊢
    generalize b % m₁ = ub at hub hdb hpab ⊢
    generalize a / m₁ = ja at hja hda hpab ⊢
    generalize b / m₁ = jb at hja hjb hdb hpab ⊢
    refine ⟨?_, by omega, by omega, by omega, by omega, fun he => ?_⟩
    · rw [Nat.cast_sub hpab.le]
      push_cast
      ring
    · have : ja = jb := by omega
      subst this
      omega
  choose ρ hρ using hrep
  let π : ℕ → ZMod m₁ × ZMod m₂ := fun d => (((ρ d).1 : ZMod m₁), ((ρ d).2 : ZMod m₂))
  -- `π` sends block sums to nonzero elements.
  have hπ0 : ∀ d ∈ blockSums (liftSeq m₁ m₂ M), π d ≠ 0 := by
    intro d hd h0
    obtain ⟨-, -, hr2, he1, he2, hpos⟩ := hρ d hd
    obtain ⟨h1, h2⟩ := Prod.mk_eq_zero.mp h0
    rw [CharP.intCast_eq_zero_iff (ZMod m₂) m₂] at h2
    have hr := hpos (Int.eq_zero_of_dvd_of_nonneg_of_lt he1 (by exact_mod_cast he2) h2)
    rw [CharP.intCast_eq_zero_iff (ZMod m₁) m₁] at h1
    have := Int.eq_zero_of_dvd_of_nonneg_of_lt hr.le (by exact_mod_cast hr2) h1
    omega
  -- `π` sends a sum of block sums to the sum in the group.
  have hadd : ∀ x ∈ blockSums (liftSeq m₁ m₂ M), ∀ y ∈ blockSums (liftSeq m₁ m₂ M),
      x + y ∈ blockSums (liftSeq m₁ m₂ M) → π x + π y = π (x + y) := by
    intro x hx y hy hxy
    obtain ⟨hdx, hx1, hx2, -, -, -⟩ := hρ x hx
    obtain ⟨hdy, hy1, hy2, -, -, -⟩ := hρ y hy
    obtain ⟨hdz, hz1, hz2, -, -, -⟩ := hρ (x + y) hxy
    push_cast at hdz
    have hid : (ρ x).1 + (ρ y).1 - (ρ (x + y)).1 =
        M * ((ρ (x + y)).2 - (ρ x).2 - (ρ y).2) := by
      linear_combination hdz - hdx - hdy
    have hr : (ρ x).1 + (ρ y).1 - (ρ (x + y)).1 = 0 :=
      Int.eq_zero_of_abs_lt_dvd ⟨_, hid⟩ (abs_lt.mpr ⟨by omega, by omega⟩)
    rw [hr] at hid
    have he : (ρ (x + y)).2 = (ρ x).2 + (ρ y).2 := by
      rcases mul_eq_zero.mp hid.symm with h | h
      · omega
      · linarith
    have hr' : (ρ (x + y)).1 = (ρ x).1 + (ρ y).1 := by linarith
    simp only [π, Prod.mk_add_mk, hr', he, Int.cast_add]
  refine ⟨fun i => {d | d ∈ blockSums (liftSeq m₁ m₂ M) ∧ π d ∈ C i}, fun i => ?_, ?_⟩
  · rintro x ⟨hx, hxC⟩ y ⟨hy, hyC⟩ ⟨hxy, hxyC⟩
    rw [← hadd x hx y hy hxy] at hxyC
    exact hC i _ hxC _ hyC hxyC
  · intro d hd
    obtain ⟨i, hi⟩ := hcov (π d) (hπ0 d hd)
    exact Set.mem_iUnion.2 ⟨i, hd, hi⟩
