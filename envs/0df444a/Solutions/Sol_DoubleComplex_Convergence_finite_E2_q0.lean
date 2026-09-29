-- Prove2me | solution 1 for DoubleComplex.Convergence.finite_E2_q0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/45549571-13b7-57d6-adde-3f990aad4a75

import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DoubleComplex_Convergence_finite_E2_q0

set_option autoImplicit false

universe u

noncomputable section

namespace DoubleComplex
p2m_export "DoubleComplex" "E₂I SubQuot Convergence"
p2m_open "DoubleComplex"

section Extract

variable {R : Type u} [CommRing R]

theorem subquot_finite [IsNoetherianRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (s : SubQuot R M) : Module.Finite R s.carrier := by
  haveI : IsNoetherian R M := isNoetherian_of_isNoetherianRing_of_finite R M
  haveI : Module.Finite R ↥s.Z := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  exact Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.Quotient.mk_surjective _)

theorem filt_finite [IsNoetherianRing R]
    {M : Type u} [AddCommGroup M] [Module R M] {N : ℕ} (F : Fin (N + 1) → Submodule R M)
    (hF₀ : F 0 = ⊥) (hFmono : Monotone F)
    (hFgr : ∀ i : Fin N,
      Module.Finite R (↥(F i.succ) ⧸ (F i.castSucc).comap (F i.succ).subtype)) :
    ∀ i, Module.Finite R ↥(F i) := by
  intro i
  induction i using Fin.induction with
  | zero => rw [hF₀]; exact Module.Finite.iff_fg.mpr Submodule.fg_bot
  | succ j ih =>
    haveI := ih
    haveI hS : Module.Finite R ↥((F j.castSucc).comap (F j.succ).subtype) :=
      Module.Finite.equiv
        (Submodule.comapSubtypeEquivOfLe (hFmono (Fin.castSucc_le_succ j))).symm
    haveI hQ : Module.Finite R (↥(F j.succ) ⧸ (F j.castSucc).comap (F j.succ).subtype) := hFgr j
    exact Module.Finite.of_submodule_quotient ((F j.castSucc).comap (F j.succ).subtype)

namespace Convergence p2m_export "DoubleComplex.Convergence" "Bfilt_mono Einf Hfilt hZ0 Bfilt_gr Bfilt_top Bfilt_bot Hfilt_gr Bfilt" end Convergence
p2m_open_scoped "DoubleComplex.Convergence" in

theorem Convergence.finite_E2_q0 [IsNoetherianRing R]
    {E₂ : ℕ → ℕ → Type u} [∀ p q, AddCommGroup (E₂ p q)] [∀ p q, Module R (E₂ p q)]
    {H : ℕ → Type u} [∀ n, AddCommGroup (H n)] [∀ n, Module R (H n)] {N : ℕ}
    (conv : Convergence R E₂ H N)
    (hH : ∀ n, Module.Finite R (H n)) (hE₂ : ∀ p q, 1 ≤ q → Module.Finite R (E₂ p q))
    (p : ℕ) (hp : p ≤ N) : Module.Finite R (E₂ p 0) := by

  have hBfilt : ∀ i, Module.Finite R ↥(conv.Bfilt p i) := by
    refine filt_finite (conv.Bfilt p) (conv.Bfilt_bot p)
      (conv.Bfilt_mono p) (fun i => ?_)
    obtain ⟨p', q', hq', s, ⟨e⟩⟩ := conv.Bfilt_gr p i
    haveI := hE₂ p' q' hq'
    haveI := subquot_finite s
    exact Module.Finite.equiv e.symm

  haveI hEinf : Module.Finite R (conv.Einf p 0).carrier := by
    let pF : Fin (N + 1) := ⟨p, Nat.lt_succ_of_le hp⟩
    obtain ⟨e⟩ := conv.Hfilt_gr pF
    haveI := hH p
    haveI : IsNoetherian R (H p) := isNoetherian_of_isNoetherianRing_of_finite R (H p)
    haveI : Module.Finite R ↥(conv.Hfilt p pF.succ) :=
      Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
    haveI hgrH : Module.Finite R
        (↥(conv.Hfilt p pF.succ) ⧸
          (conv.Hfilt p pF.castSucc).comap (conv.Hfilt p pF.succ).subtype) :=
      Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.Quotient.mk_surjective _)
    exact Module.Finite.equiv e

  haveI hB : Module.Finite R ↥(conv.Einf p 0).B := conv.Bfilt_top p ▸ hBfilt (Fin.last N)
  haveI hBc : Module.Finite R ↥((conv.Einf p 0).B.comap (conv.Einf p 0).Z.subtype) :=
    Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe (conv.Einf p 0).hBZ).symm
  haveI hZ : Module.Finite R ↥(conv.Einf p 0).Z :=
    Module.Finite.of_submodule_quotient ((conv.Einf p 0).B.comap (conv.Einf p 0).Z.subtype)
  haveI : Module.Finite R ↥(⊤ : Submodule R (E₂ p 0)) := conv.hZ0 p ▸ hZ
  exact Module.Finite.equiv Submodule.topEquiv

end Extract

end DoubleComplex

theorem solution {R : Type u} [CommRing R] [IsNoetherianRing R]
    {E₂ : ℕ → ℕ → Type u} [∀ p q, AddCommGroup (E₂ p q)] [∀ p q, Module R (E₂ p q)]
    {H : ℕ → Type u} [∀ n, AddCommGroup (H n)] [∀ n, Module R (H n)] {N : ℕ}
    (conv : DoubleComplex.Convergence R E₂ H N)
    (hH : ∀ n, Module.Finite R (H n)) (hE₂ : ∀ p q, 1 ≤ q → Module.Finite R (E₂ p q))
    (p : ℕ) (hp : p ≤ N) : Module.Finite R (E₂ p 0) :=
  DoubleComplex.Convergence.finite_E2_q0 conv hH hE₂ p hp

end

end S_DoubleComplex_Convergence_finite_E2_q0
end P2MW
export P2MW.S_DoubleComplex_Convergence_finite_E2_q0 (solution)
