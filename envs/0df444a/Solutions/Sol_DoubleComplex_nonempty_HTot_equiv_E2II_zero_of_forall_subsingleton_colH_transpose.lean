-- Prove2me | solution 1 for DoubleComplex.nonempty_HTot_equiv_E2II_zero_of_forall_subsingleton_colH_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/6c966cfe-cecc-5272-8363-454728274b98

import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DoubleComplex_nonempty_HTot_equiv_E2II_zero_of_forall_subsingleton_colH_transpose

set_option autoImplicit false

universe u

noncomputable section

namespace G1SOL

open DoubleComplex

section Generic

variable {R : Type u} [CommRing R] {D : DoubleComplex.Bounded R}

theorem dTot_single_apply_succ {n pp q : ℕ} (h : pp + 1 + q = n + 1)
    (j : DoubleComplex.Diag n) (x : D.C j.1.1 j.1.2) (hne : pp + 1 ≠ j.1.1) :
    DoubleComplex.dTot D n
        (Pi.single (M := fun i : DoubleComplex.Diag n => D.C i.1.1 i.1.2) j x)
        ⟨(pp + 1, q), h⟩
      = D.dH pp q (Pi.single (M := fun i : DoubleComplex.Diag n => D.C i.1.1 i.1.2)
          j x ⟨(pp, q), by omega⟩) := by
  match q, h with
  | 0, h => exact DoubleComplex.dTot_apply_succ_zero h _
  | q' + 1, h =>
    rw [DoubleComplex.dTot_apply_succ_succ]
    refine add_eq_left.mpr ?_
    rw [Pi.single_eq_of_ne (fun heq => hne (congrArg (fun i => i.1.1) heq)), map_zero, smul_zero]

end Generic

section Main

variable {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R)

def φ (b : ℕ) : colH (transpose D) b 0 ≃ₗ[R] LinearMap.ker ((transpose D).dV b 0) :=
  Submodule.quotEquivOfEqBot _ rfl

def aug (b : ℕ) : colH (transpose D) b 0 →ₗ[R] D.C 0 b :=
  (LinearMap.ker ((transpose D).dV b 0)).subtype ∘ₗ (φ D b).toLinearMap

theorem aug_mk (b : ℕ) (z : LinearMap.ker ((transpose D).dV b 0)) :
    aug D b (Submodule.Quotient.mk z) = z.1 := by
  simp [aug, φ]
  rfl

theorem dH_aug (b : ℕ) (y : colH (transpose D) b 0) : D.dH 0 b (aug D b y) = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [aug_mk]
  exact LinearMap.mem_ker.mp z.2

theorem aug_injective (b : ℕ) : Function.Injective (aug D b) := fun _ _ h =>
  (φ D b).injective (Subtype.ext h)

theorem exists_aug_eq (b : ℕ) (x : D.C 0 b) (hx : D.dH 0 b x = 0) : ∃ y, aug D b y = x :=
  ⟨Submodule.Quotient.mk ⟨x, LinearMap.mem_ker.mpr hx⟩, aug_mk D b _⟩

theorem dV_comp_aug (b : ℕ) :
    D.dV 0 b ∘ₗ aug D b = aug D (b + 1) ∘ₗ colHdH (transpose D) b 0 := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [LinearMap.comp_apply, LinearMap.comp_apply, aug_mk]
  simp only [colHdH, Submodule.mapQ_apply, aug_mk]
  try rfl

theorem exists_dH_eq (hex : ∀ p q : ℕ, Subsingleton (colH (transpose D) q (p + 1))) (P Q : ℕ)
    (x : D.C (P + 1) Q) (hx : D.dH (P + 1) Q x = 0) : ∃ b : D.C P Q, D.dH P Q b = x := by
  haveI := hex P Q
  have hz : (⟨x, LinearMap.mem_ker.mpr hx⟩ : LinearMap.ker ((transpose D).dV Q (P + 1))) ∈
      colB (transpose D) Q (P + 1) :=
    (Submodule.Quotient.mk_eq_zero _).mp (Subsingleton.elim _ _)
  simp only [colB, Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_range] at hz
  exact hz

def edge (m : ℕ) : colH (transpose D) m 0 →ₗ[R] DoubleComplex.Tot D m :=
  (LinearMap.single R (fun i : DoubleComplex.Diag m => D.C i.1.1 i.1.2) ⟨(0, m), Nat.zero_add m⟩).comp (aug D m)

theorem edge_apply_zero {m : ℕ} (h : 0 + m = m) (y : colH (transpose D) m 0) :
    edge D m y ⟨(0, m), h⟩ = aug D m y :=
  Pi.single_eq_same (M := fun i : DoubleComplex.Diag m => D.C i.1.1 i.1.2) _ _

theorem edge_apply_pos {m p' q : ℕ} (h : p' + 1 + q = m) (y : colH (transpose D) m 0) :
    edge D m y ⟨(p' + 1, q), h⟩ = 0 := by
  show Pi.single (M := fun i : DoubleComplex.Diag m => D.C i.1.1 i.1.2)
    ⟨(0, m), Nat.zero_add m⟩ (aug D m y) ⟨(p' + 1, q), h⟩ = 0
  exact Pi.single_eq_of_ne
    (fun heq => by simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq; omega) _

variable (hex : ∀ p q : ℕ, Subsingleton (colH (transpose D) q (p + 1)))

theorem edge_chain (n : ℕ) :
    DoubleComplex.dTot D n ∘ₗ edge D n
      = edge D (n + 1) ∘ₗ colHdH (transpose D) n 0 := by
  refine LinearMap.ext fun y => funext fun ⟨⟨pp, q⟩, h⟩ => ?_
  show DoubleComplex.dTot D n (edge D n y) ⟨(pp, q), h⟩
    = edge D (n + 1) (colHdH (transpose D) n 0 y) ⟨(pp, q), h⟩
  match pp, q, h with
  | 0, q' + 1, h =>
    obtain rfl : q' = n := by omega
    rw [DoubleComplex.dTot_apply_zero_succ, edge_apply_zero, edge_apply_zero]
    exact LinearMap.congr_fun (dV_comp_aug D q') y
  | p' + 1, 0, h =>
    obtain rfl : p' = n := by omega
    rw [DoubleComplex.dTot_apply_succ_zero, edge_apply_pos]
    rcases p' with _ | p''
    · rw [edge_apply_zero]
      exact dH_aug D 0 y
    · rw [edge_apply_pos, map_zero]
  | p' + 1, q' + 1, h =>
    rw [DoubleComplex.dTot_apply_succ_succ, edge_apply_pos, edge_apply_pos, map_zero, smul_zero, add_zero]
    rcases p' with _ | p''
    · obtain rfl : q' + 1 = n := by omega
      rw [edge_apply_zero]
      exact dH_aug D (q' + 1) y
    · rw [edge_apply_pos, map_zero]

include hex in

theorem stair_surj (n : ℕ)
    (c : DoubleComplex.Tot D (n + 1)) (hc : DoubleComplex.dTot D (n + 1) c = 0) :
    ∃ (y : colH (transpose D) (n + 1) 0) (bb : DoubleComplex.Tot D n),
      colHdH (transpose D) (n + 1) 0 y = 0 ∧
      c = edge D (n + 1) y + DoubleComplex.dTot D n bb := by
  suffices H : ∀ P, ∀ c : DoubleComplex.Tot D (n + 1),
      DoubleComplex.dTot D (n + 1) c = 0 →
      (∀ pp q h, P < pp → c ⟨(pp, q), h⟩ = 0) →
      ∃ y bb, colHdH (transpose D) (n + 1) 0 y = 0 ∧
        c = edge D (n + 1) y + DoubleComplex.dTot D n bb from
    H (n + 1) c hc fun pp q hpq hp => absurd hpq (by omega)
  intro P
  induction P with
  | zero =>
    intro c hc htop
    have hdH : D.dH 0 (n + 1) (c ⟨(0, n + 1), by omega⟩) = 0 := by
      have h1 := congrFun hc ⟨(1, n + 1), by omega⟩
      rwa [Pi.zero_apply, DoubleComplex.dTot_apply_succ_succ,
        htop 1 n (by omega) one_pos, map_zero, smul_zero, add_zero] at h1
    obtain ⟨y, hy⟩ := exists_aug_eq D (n + 1) _ hdH
    have hdy : colHdH (transpose D) (n + 1) 0 y = 0 := by
      have hcomm : D.dV 0 (n + 1) (aug D (n + 1) y)
          = aug D (n + 2) (colHdH (transpose D) (n + 1) 0 y) :=
        LinearMap.congr_fun (dV_comp_aug D (n + 1)) y
      refine aug_injective D (n + 2) ?_
      rw [map_zero, ← hcomm, hy]
      have h0 := congrFun hc ⟨(0, n + 2), by omega⟩
      rwa [Pi.zero_apply, DoubleComplex.dTot_apply_zero_succ] at h0
    refine ⟨y, 0, hdy, funext fun ⟨⟨pp, q⟩, hpq⟩ => ?_⟩
    simp only [Pi.add_apply, map_zero, Pi.zero_apply, add_zero]
    match pp, hpq with
    | 0, hpq =>
      obtain rfl : q = n + 1 := by omega
      rw [edge_apply_zero, hy]
    | p' + 1, hpq =>
      rw [htop (p' + 1) q hpq (Nat.succ_pos _), edge_apply_pos]
  | succ P ih =>
    intro c hc htop
    by_cases hPn : P + 1 ≤ n + 1
    · have hdH : ∀ Q (hQ : P + 1 + Q = n + 1),
          D.dH (P + 1) Q (c ⟨(P + 1, Q), hQ⟩) = 0 :=
        fun Q hQ => by
          have h1 : DoubleComplex.dTot D (n + 1) c ⟨(P + 2, Q), by omega⟩ = 0 := congrFun hc _
          match Q, hQ, h1 with
          | 0, hQ, h1 => rwa [DoubleComplex.dTot_apply_succ_zero] at h1
          | m + 1, hQ, h1 =>
            rwa [DoubleComplex.dTot_apply_succ_succ,
              htop (P + 2) m (by omega) (by omega), map_zero, smul_zero, add_zero] at h1
      obtain ⟨bτ, hbτ⟩ := exists_dH_eq D hex P (n - P) _ (hdH (n - P) (by omega))
      set b' : DoubleComplex.Tot D n :=
        Pi.single ⟨(P, n - P), by omega⟩ bτ
      have hb'ne : ∀ pp q h, (pp, q) ≠ (P, n - P) → b' ⟨(pp, q), h⟩ = 0 := fun pp q h hne =>
        Pi.single_eq_of_ne (fun heq => hne (by simp only [Subtype.mk.injEq] at heq; exact heq)) _
      have hdHb' : ∀ Q (hQ : P + 1 + Q = n + 1),
          DoubleComplex.dTot D n b' ⟨(P + 1, Q), hQ⟩ = c ⟨(P + 1, Q), hQ⟩ := fun Q hQ => by
        obtain rfl : Q = n - P := by omega
        rw [show b' = _ from rfl,
          dTot_single_apply_succ hQ _ _ (by simp), Pi.single_eq_same]
        exact hbτ
      set c' := c - DoubleComplex.dTot D n b'
      have hc' : DoubleComplex.dTot D (n + 1) c' = 0 := by
        simp only [c', map_sub, hc, zero_sub, neg_eq_zero]
        exact LinearMap.congr_fun (DoubleComplex.dTot_comp_dTot D n) b'
      have htop' : ∀ pp q h, P < pp → c' ⟨(pp, q), h⟩ = 0 := by
        intro pp q hpq hp
        simp only [c', Pi.sub_apply, sub_eq_zero]
        rcases (Nat.lt_iff_add_one_le.mp hp).eq_or_lt with heq | hlt
        · exact heq ▸ (hdHb' q (heq ▸ hpq)).symm
        · rw [htop pp q hpq (by omega)]
          match pp, q, hpq with
          | p' + 1, 0, _ =>
            rw [DoubleComplex.dTot_apply_succ_zero,
              hb'ne p' 0 (by omega) (by intro heq; injection heq; omega), map_zero]
          | p' + 1, q' + 1, _ =>
            rw [DoubleComplex.dTot_apply_succ_succ,
              hb'ne p' (q'+1) (by omega) (by intro heq; injection heq; omega),
              hb'ne (p'+1) q' (by omega) (by intro heq; injection heq; omega),
              map_zero, map_zero, smul_zero, add_zero]
      obtain ⟨y, b₀, hdy, hceq'⟩ := ih c' hc' htop'
      exact ⟨y, b₀ + b', hdy, by rw [map_add, ← add_assoc, ← hceq']; simp only [c', sub_add_cancel]⟩
    · exact ih c hc fun pp q hpq hp => htop pp q hpq (lt_of_le_of_lt (by omega) hp)

include hex in

theorem stair_inj (n : ℕ) (y : colH (transpose D) (n + 1) 0)
    (bb : DoubleComplex.Tot D n)
    (hb : edge D (n + 1) y = DoubleComplex.dTot D n bb) :
    ∃ y', y = colHdH (transpose D) n 0 y' := by
  suffices H : ∀ P, ∀ bb : DoubleComplex.Tot D n,
      edge D (n + 1) y = DoubleComplex.dTot D n bb →
      (∀ pp q h, P < pp → bb ⟨(pp, q), h⟩ = 0) →
      ∃ y', y = colHdH (transpose D) n 0 y' from
    H n bb hb fun pp q hpq hp => absurd hpq (by omega)
  intro P
  induction P with
  | zero =>
    intro bb hb htop
    have hdH : D.dH 0 n (bb ⟨(0, n), by omega⟩) = 0 := by
      have h1 := congrFun hb ⟨(1, n), by omega⟩
      rcases n with _ | n'
      · rwa [edge_apply_pos, DoubleComplex.dTot_apply_succ_zero, eq_comm] at h1
      · rwa [edge_apply_pos, DoubleComplex.dTot_apply_succ_succ,
          htop 1 n' (by omega) one_pos, map_zero, smul_zero, add_zero, eq_comm] at h1
    obtain ⟨w, hw⟩ := exists_aug_eq D n _ hdH
    refine ⟨w, aug_injective D (n + 1) ?_⟩
    have h0 := congrFun hb ⟨(0, n + 1), by omega⟩
    rw [edge_apply_zero, DoubleComplex.dTot_apply_zero_succ] at h0
    have hcomm : D.dV 0 n (aug D n w)
        = aug D (n + 1) (colHdH (transpose D) n 0 w) :=
      LinearMap.congr_fun (dV_comp_aug D n) w
    rw [← hcomm, hw]
    exact h0
  | succ P ih =>
    intro bb hb htop
    by_cases hPn : P + 1 ≤ n
    · rcases n with _ | n'
      · omega
      have hdH : ∀ Q (hQ : P + 1 + Q = n' + 1),
          D.dH (P + 1) Q (bb ⟨(P + 1, Q), hQ⟩) = 0 := fun Q hQ => by
        have h1 : DoubleComplex.dTot D (n' + 1) bb ⟨(P + 2, Q), by omega⟩ = 0 := by
          rw [← congrFun hb _, edge_apply_pos]
        match Q, hQ, h1 with
        | 0, hQ, h1 => rwa [DoubleComplex.dTot_apply_succ_zero] at h1
        | m + 1, hQ, h1 =>
          rwa [DoubleComplex.dTot_apply_succ_succ,
            htop (P + 2) m (by omega) (by omega), map_zero, smul_zero, add_zero] at h1
      obtain ⟨bτ, hbτ⟩ := exists_dH_eq D hex P (n' - P) _ (hdH (n' - P) (by omega))
      set b'' : DoubleComplex.Tot D n' :=
        Pi.single ⟨(P, n' - P), by omega⟩ bτ
      have hb''ne : ∀ pp q h, (pp, q) ≠ (P, n' - P) → b'' ⟨(pp, q), h⟩ = 0 := fun pp q h hne =>
        Pi.single_eq_of_ne (fun heq => hne (by simp only [Subtype.mk.injEq] at heq; exact heq)) _
      have hdHb'' : ∀ Q (hQ : P + 1 + Q = n' + 1),
          DoubleComplex.dTot D n' b'' ⟨(P + 1, Q), hQ⟩ = bb ⟨(P + 1, Q), hQ⟩ := fun Q hQ => by
        obtain rfl : Q = n' - P := by omega
        rw [show b'' = _ from rfl,
          dTot_single_apply_succ hQ _ _ (by simp), Pi.single_eq_same]
        exact hbτ
      refine ih (bb - DoubleComplex.dTot D n' b'') ?_ ?_
      · rw [map_sub, ← LinearMap.comp_apply, DoubleComplex.dTot_comp_dTot,
          LinearMap.zero_apply, sub_zero, hb]
      · intro pp q hpq hp
        simp only [Pi.sub_apply, sub_eq_zero]
        rcases (Nat.lt_iff_add_one_le.mp hp).eq_or_lt with heq | hlt
        · exact heq ▸ (hdHb'' q (heq ▸ hpq)).symm
        · rw [htop pp q hpq (by omega)]
          match pp, q, hpq with
          | p' + 1, 0, _ =>
            rw [DoubleComplex.dTot_apply_succ_zero,
              hb''ne p' 0 (by omega) (by intro heq; injection heq; omega), map_zero]
          | p' + 1, q' + 1, _ =>
            rw [DoubleComplex.dTot_apply_succ_succ,
              hb''ne p' (q'+1) (by omega) (by intro heq; injection heq; omega),
              hb''ne (p'+1) q' (by omega) (by intro heq; injection heq; omega),
              map_zero, map_zero, smul_zero, add_zero]
    · exact ih bb hb fun pp q hpq hp => htop pp q hpq (lt_of_le_of_lt (by omega) hp)

def Hedge (n : ℕ) :
    E₂I (transpose D) (n + 1) 0 →ₗ[R] DoubleComplex.HTot D (n + 1) :=
  Submodule.mapQ _ _
    ((edge D (n + 1)).restrict fun y hy => LinearMap.mem_ker.mpr <| by
      have hy' : colHdH (transpose D) (n + 1) 0 y = 0 := LinearMap.mem_ker.mp hy
      have hch := LinearMap.congr_fun (edge_chain D (n + 1)) y
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hy', map_zero] at hch
      exact hch)
    (by
      rintro x ⟨y', hy'⟩
      refine ⟨edge D n y', ?_⟩
      have hch := LinearMap.congr_fun (edge_chain D n) y'
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at hch
      exact hch.trans (congrArg _ hy'))

include hex in

def HTotSuccEquiv (n : ℕ) :
    DoubleComplex.HTot D (n + 1) ≃ₗ[R] E₂I (transpose D) (n + 1) 0 :=
  (LinearEquiv.ofBijective (Hedge D n)
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro x hmap
      obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      simp only [Hedge, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hmap
      obtain ⟨bb, hbb⟩ := hmap
      obtain ⟨y', hy'⟩ := stair_inj D hex n y bb hbb.symm
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y', hy'.symm⟩,
     fun x => by
      obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨y, bb, hdy, hceq⟩ := stair_surj D hex n c (LinearMap.mem_ker.mp hc)
      refine ⟨Submodule.Quotient.mk ⟨y, LinearMap.mem_ker.mpr hdy⟩, ?_⟩
      simp only [Hedge, Submodule.mapQ_apply, Submodule.Quotient.eq]
      exact ⟨-bb, by
        show DoubleComplex.dTot D n (-bb) = edge D (n + 1) y - c
        rw [map_neg, hceq, sub_add_eq_sub_sub, sub_self, zero_sub]⟩⟩).symm

def HTotZeroEquiv :
    DoubleComplex.HTot D 0 ≃ₗ[R] LinearMap.ker (colHdH (transpose D) 0 0) :=
  (Submodule.quotEquivOfEqBot _ rfl).trans
    (LinearEquiv.ofBijective
      (((edge D 0).comp
        (LinearMap.ker (colHdH (transpose D) 0 0)).subtype).codRestrict
        (LinearMap.ker (DoubleComplex.dTot D 0))
        fun y => LinearMap.mem_ker.mpr <| by
          have hch := LinearMap.congr_fun (edge_chain D 0) y.1
          rw [LinearMap.comp_apply, LinearMap.comp_apply] at hch
          exact hch.trans ((congrArg _ (LinearMap.mem_ker.mp y.2)).trans (map_zero _)))
      ⟨fun y₁ y₂ hy => Subtype.ext (aug_injective D 0
          ((edge_apply_zero D (Nat.zero_add 0) y₁.1).symm.trans
            ((congrFun (Subtype.ext_iff.mp hy) ⟨(0,0), Nat.zero_add 0⟩).trans
              (edge_apply_zero D (Nat.zero_add 0) y₂.1)))),
       fun ⟨c, hc⟩ => by
          have hdH : D.dH 0 0 (c ⟨(0,0), Nat.zero_add 0⟩) = 0 := by
            have h1 := congrFun (LinearMap.mem_ker.mp hc) ⟨(1, 0), rfl⟩
            rwa [Pi.zero_apply, DoubleComplex.dTot_apply_succ_zero] at h1
          obtain ⟨y, hy⟩ := exists_aug_eq D 0 _ hdH
          have hdy : colHdH (transpose D) 0 0 y = 0 := by
            have hcomm : D.dV 0 0 (aug D 0 y)
                = aug D 1 (colHdH (transpose D) 0 0 y) :=
              LinearMap.congr_fun (dV_comp_aug D 0) y
            refine aug_injective D 1 ?_
            rw [map_zero, ← hcomm, hy]
            have h0 := congrFun (LinearMap.mem_ker.mp hc) ⟨(0, 1), rfl⟩
            rwa [Pi.zero_apply, DoubleComplex.dTot_apply_zero_succ] at h0
          refine ⟨⟨y, LinearMap.mem_ker.mpr hdy⟩, Subtype.ext (funext fun ⟨⟨pp,q⟩,hpq⟩ => ?_)⟩
          obtain ⟨rfl, rfl⟩ : pp = 0 ∧ q = 0 := by omega
          exact (edge_apply_zero D (Nat.zero_add 0) y).trans hy⟩).symm

end Main

end G1SOL

end

theorem G1main
    {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R)
    (hex : ∀ p q : ℕ, Subsingleton (DoubleComplex.colH (DoubleComplex.transpose D) q (p + 1)))
    (n : ℕ) :
    Nonempty (DoubleComplex.HTot D n ≃ₗ[R] DoubleComplex.E₂II D 0 n) := by
  cases n with
  | zero => exact ⟨(G1SOL.HTotZeroEquiv D).trans (Submodule.quotEquivOfEqBot _ rfl).symm⟩
  | succ k => exact ⟨G1SOL.HTotSuccEquiv D hex k⟩

theorem solution
    {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R)
    (hex : ∀ p q : ℕ, Subsingleton (DoubleComplex.colH (DoubleComplex.transpose D) q (p + 1)))
    (n : ℕ) :
    Nonempty (DoubleComplex.HTot D n ≃ₗ[R] DoubleComplex.E₂II D 0 n) :=
  G1main D hex n

end S_DoubleComplex_nonempty_HTot_equiv_E2II_zero_of_forall_subsingleton_colH_transpose
end P2MW
export P2MW.S_DoubleComplex_nonempty_HTot_equiv_E2II_zero_of_forall_subsingleton_colH_transpose (solution)
