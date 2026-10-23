-- Prove2me | solution 1 for FRV.uuv_abelianization
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-23T01:46:06.284053+00:00
-- url     : https://prove2.me/submissions/b02811fe-a32a-4c5e-84a1-3c6f2bd5cb87

import Mathlib
import Definitions.Def_FRV_alg
import Definitions.Def_FRV_tor

open FRV


/-- Degenerate world: every group is `Unit`. -/
def frv84_wU (n : ℕ) : ForbiddenWorld n 1 Unit Unit Unit Unit Unit Unit Unit where
  rho := fun _ => 1
  sigma := fun _ _ => 1
  hk := one_pos
  N1 := ⊤
  N2 := ⊤
  NM := ⊤
  N1normal := inferInstance
  N2normal := inferInstance
  NMnormal := inferInstance
  f1mem := fun _ _ _ => Subgroup.mem_top _
  f2mem := fun _ _ _ => Subgroup.mem_top _
  p1 := 1
  p1ker := MonoidHom.ker_one
  p1surj := fun _ => ⟨1, rfl⟩
  p2 := 1
  p2ker := MonoidHom.ker_one
  p2surj := fun _ => ⟨1, rfl⟩
  pm := 1
  pmker := MonoidHom.ker_one
  pmsurj := fun _ => ⟨1, rfl⟩
  pm1 := 1
  pm1ker := by simp
  pm1surj := fun _ => ⟨1, rfl⟩
  pm2 := 1
  pm2ker := by simp
  pm2surj := fun _ => ⟨1, rfl⟩
  pu := 1
  puker := by simp
  pusurj := fun _ => ⟨1, rfl⟩
  theta := MulEquiv.refl _
  thetaRho := fun _ => rfl
  thetaSigma := fun _ _ => rfl
  zeta := fun _ => MulEquiv.refl _
  zetaRho := fun _ _ => rfl
  zetaSigma := fun _ _ _ => rfl
  uuvPerm := 1

abbrev Z2 := Multiplicative (ZMod 2)

/-- World with `N1 = ⊥`, `N2 = ⊤`, `NM = ⊥` on `V = ZMod 2`, all generators trivial. -/
def frv84_wQ : ForbiddenWorld 3 1 Z2 Z2 Unit Z2 Unit Z2 Unit where
  rho := fun _ => 1
  sigma := fun _ _ => 1
  hk := one_pos
  N1 := ⊥
  N2 := ⊤
  NM := ⊥
  N1normal := inferInstance
  N2normal := inferInstance
  NMnormal := inferInstance
  f1mem := fun _ _ _ => by simp
  f2mem := fun _ _ _ => Subgroup.mem_top _
  p1 := MonoidHom.id _
  p1ker := MonoidHom.ker_id
  p1surj := fun y => ⟨y, rfl⟩
  p2 := 1
  p2ker := MonoidHom.ker_one
  p2surj := fun _ => ⟨1, rfl⟩
  pm := MonoidHom.id _
  pmker := MonoidHom.ker_id
  pmsurj := fun y => ⟨y, rfl⟩
  pm1 := MonoidHom.id _
  pm1ker := by simp
  pm1surj := fun y => ⟨y, rfl⟩
  pm2 := 1
  pm2ker := by simp
  pm2surj := fun _ => ⟨1, rfl⟩
  pu := 1
  puker := by simp
  pusurj := fun _ => ⟨1, rfl⟩
  theta := MulEquiv.refl _
  thetaRho := fun _ => rfl
  thetaSigma := fun _ _ => by simp
  zeta := fun _ => MulEquiv.refl _
  zetaRho := fun _ _ => rfl
  zetaSigma := fun _ _ _ => by simp
  uuvPerm := 1

/-- the 3-cycle `0 → 1 → 2 → 0` -/
def frv84_c : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

/-- World on `n = 1` (no generators) with `theta` = conjugation by a 3-cycle in `S₃`. -/
def frv84_wT : ForbiddenWorld 1 1 (Equiv.Perm (Fin 3)) Unit Unit Unit Unit Unit Unit where
  rho := fun i => i.elim0
  sigma := fun i => i.elim0
  hk := one_pos
  N1 := ⊤
  N2 := ⊤
  NM := ⊤
  N1normal := inferInstance
  N2normal := inferInstance
  NMnormal := inferInstance
  f1mem := fun _ _ _ => Subgroup.mem_top _
  f2mem := fun _ _ _ => Subgroup.mem_top _
  p1 := 1
  p1ker := MonoidHom.ker_one
  p1surj := fun _ => ⟨1, rfl⟩
  p2 := 1
  p2ker := MonoidHom.ker_one
  p2surj := fun _ => ⟨1, rfl⟩
  pm := 1
  pmker := MonoidHom.ker_one
  pmsurj := fun _ => ⟨1, rfl⟩
  pm1 := 1
  pm1ker := by simp
  pm1surj := fun _ => ⟨1, rfl⟩
  pm2 := 1
  pm2ker := by simp
  pm2surj := fun _ => ⟨1, rfl⟩
  pu := 1
  puker := by simp
  pusurj := fun _ => ⟨1, rfl⟩
  theta := MulAut.conj frv84_c
  thetaRho := fun i => i.elim0
  thetaSigma := fun i => i.elim0
  zeta := fun _ => MulEquiv.refl _
  zetaRho := fun _ i => i.elim0
  zetaSigma := fun _ i => i.elim0
  uuvPerm := 1

theorem frv84_theta_not_inv : ¬ IsInvolutive frv84_wT.theta := by
  intro h
  have := h (Equiv.swap 0 1)
  revert this
  simp only [frv84_wT, MulAut.conj_apply]
  decide

theorem frv84_not_surj (n : ℕ) (hn : 2 ≤ n) :
    ¬ ∀ p : Equiv.Perm (Fin n), ∃ x : Unit, (frv84_wU n).uuvPerm x = p := by
  intro h
  obtain ⟨x, hx⟩ := h (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩)
  have h2 := congrArg (fun p : Equiv.Perm (Fin n) => p ⟨0, by omega⟩) hx
  simp [frv84_wU, Equiv.swap_apply_left] at h2

theorem frv84_noiso : ¬ ∃ e : Z2 ≃* Unit, True := by
  rintro ⟨e, -⟩
  have := e.injective (Subsingleton.elim (e 1) (e (Multiplicative.ofAdd 1)))
  revert this; decide

theorem solution : ¬ (∀ {n k : ℕ} {V Q1 Q2 QM1 QM2 Mk U : Type}
    [Group V] [Group Q1] [Group Q2] [Group QM1] [Group QM2] [Group Mk] [Group U]
    (W : ForbiddenWorld n k V Q1 Q2 QM1 QM2 Mk U) (hn : 3 ≤ n),
    ∃ ab : U →* Multiplicative ((Fin k → ℤ) × ZMod 2),
      (∀ y : Multiplicative ((Fin k → ℤ) × ZMod 2), ∃ x : U, ab x = y) ∧
      MonoidHom.ker ab = Derived U) :=
  by
  intro h
  obtain ⟨ab, hs, -⟩ := h (frv84_wU 3) le_rfl
  obtain ⟨x, hx⟩ := hs (Multiplicative.ofAdd (0, 1))
  rw [Subsingleton.elim x 1, map_one] at hx
  have := congrArg (fun z => (Multiplicative.toAdd z).2) hx
  revert this; decide
