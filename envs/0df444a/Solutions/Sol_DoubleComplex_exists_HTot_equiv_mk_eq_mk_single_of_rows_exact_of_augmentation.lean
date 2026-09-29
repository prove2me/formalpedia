-- Prove2me | solution 1 for DoubleComplex.exists_HTot_equiv_mk_eq_mk_single_of_rows_exact_of_augmentation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/e3e00720-1b4a-5b2d-9a4a-103b49cbb659

import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DoubleComplex_exists_HTot_equiv_mk_eq_mk_single_of_rows_exact_of_augmentation

set_option autoImplicit false

universe u

noncomputable section

namespace P1SOL

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

variable {R : Type u} [CommRing R] {D : DoubleComplex.Bounded R}
variable {A : ℕ → Type u} [∀ m, AddCommGroup (A m)] [∀ m, Module R (A m)]
variable {dA : ∀ m, A m →ₗ[R] A (m + 1)} (ε : ∀ m, A m →ₗ[R] D.C 0 m)

theorem dH_aug (hker : ∀ m, LinearMap.ker (D.dH 0 m) = LinearMap.range (ε m)) (b : ℕ) (y : A b) :
    D.dH 0 b (ε b y) = 0 := by
  have h : ε b y ∈ LinearMap.ker (D.dH 0 b) := by
    rw [hker b]; exact LinearMap.mem_range_self _ _
  exact LinearMap.mem_ker.mp h

theorem exists_aug_eq (hker : ∀ m, LinearMap.ker (D.dH 0 m) = LinearMap.range (ε m)) (b : ℕ) (x : D.C 0 b) (hx : D.dH 0 b x = 0) :
    ∃ y, ε b y = x := by
  have h : x ∈ LinearMap.range (ε b) := by
    rw [← hker b]; exact LinearMap.mem_ker.mpr hx
  exact h

theorem exists_dH_eq (hrows : ∀ p m, LinearMap.ker (D.dH (p + 1) m) ≤ LinearMap.range (D.dH p m)) (P Q : ℕ)
    (x : D.C (P + 1) Q) (hx : D.dH (P + 1) Q x = 0) : ∃ b : D.C P Q, D.dH P Q b = x :=
  hrows P Q (LinearMap.mem_ker.mpr hx)

def edge (m : ℕ) : A m →ₗ[R] DoubleComplex.Tot D m :=
  (LinearMap.single R (fun i : DoubleComplex.Diag m => D.C i.1.1 i.1.2) ⟨(0, m), Nat.zero_add m⟩).comp (ε m)

theorem edge_apply_zero {m : ℕ} (h : 0 + m = m) (y : A m) :
    edge ε m y ⟨(0, m), h⟩ = ε m y :=
  Pi.single_eq_same (M := fun i : DoubleComplex.Diag m => D.C i.1.1 i.1.2) _ _

theorem edge_apply_pos {m p' q : ℕ} (h : p' + 1 + q = m) (y : A m) :
    edge ε m y ⟨(p' + 1, q), h⟩ = 0 := by
  show Pi.single (M := fun i : DoubleComplex.Diag m => D.C i.1.1 i.1.2)
    ⟨(0, m), Nat.zero_add m⟩ (ε m y) ⟨(p' + 1, q), h⟩ = 0
  exact Pi.single_eq_of_ne
    (fun heq => by simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq; omega) _

theorem edge_chain (hεd : ∀ m, D.dV 0 m ∘ₗ ε m = ε (m + 1) ∘ₗ dA m)
    (hker : ∀ m, LinearMap.ker (D.dH 0 m) = LinearMap.range (ε m)) (n : ℕ) :
    DoubleComplex.dTot D n ∘ₗ edge ε n
      = edge ε (n + 1) ∘ₗ dA n := by
  refine LinearMap.ext fun y => funext fun ⟨⟨pp, q⟩, h⟩ => ?_
  show DoubleComplex.dTot D n (edge ε n y) ⟨(pp, q), h⟩
    = edge ε (n + 1) (dA n y) ⟨(pp, q), h⟩
  match pp, q, h with
  | 0, q' + 1, h =>
    obtain rfl : q' = n := by omega
    rw [DoubleComplex.dTot_apply_zero_succ, edge_apply_zero, edge_apply_zero]
    exact LinearMap.congr_fun (hεd q') y
  | p' + 1, 0, h =>
    obtain rfl : p' = n := by omega
    rw [DoubleComplex.dTot_apply_succ_zero, edge_apply_pos]
    rcases p' with _ | p''
    · rw [edge_apply_zero]
      exact dH_aug ε hker 0 y
    · rw [edge_apply_pos, map_zero]
  | p' + 1, q' + 1, h =>
    rw [DoubleComplex.dTot_apply_succ_succ, edge_apply_pos, edge_apply_pos, map_zero, smul_zero, add_zero]
    rcases p' with _ | p''
    · obtain rfl : q' + 1 = n := by omega
      rw [edge_apply_zero]
      exact dH_aug ε hker (q' + 1) y
    · rw [edge_apply_pos, map_zero]

theorem stair_surj (hε : ∀ m, Function.Injective (ε m))
    (hεd : ∀ m, D.dV 0 m ∘ₗ ε m = ε (m + 1) ∘ₗ dA m)
    (hker : ∀ m, LinearMap.ker (D.dH 0 m) = LinearMap.range (ε m))
    (hrows : ∀ p m, LinearMap.ker (D.dH (p + 1) m) ≤ LinearMap.range (D.dH p m)) (n : ℕ)
    (c : DoubleComplex.Tot D (n + 1)) (hc : DoubleComplex.dTot D (n + 1) c = 0) :
    ∃ (y : A (n + 1)) (bb : DoubleComplex.Tot D n),
      dA (n + 1) y = 0 ∧
      c = edge ε (n + 1) y + DoubleComplex.dTot D n bb := by
  suffices H : ∀ P, ∀ c : DoubleComplex.Tot D (n + 1),
      DoubleComplex.dTot D (n + 1) c = 0 →
      (∀ pp q h, P < pp → c ⟨(pp, q), h⟩ = 0) →
      ∃ y bb, dA (n + 1) y = 0 ∧
        c = edge ε (n + 1) y + DoubleComplex.dTot D n bb from
    H (n + 1) c hc fun pp q hpq hp => absurd hpq (by omega)
  intro P
  induction P with
  | zero =>
    intro c hc htop
    have hdH : D.dH 0 (n + 1) (c ⟨(0, n + 1), by omega⟩) = 0 := by
      have h1 := congrFun hc ⟨(1, n + 1), by omega⟩
      rwa [Pi.zero_apply, DoubleComplex.dTot_apply_succ_succ,
        htop 1 n (by omega) one_pos, map_zero, smul_zero, add_zero] at h1
    obtain ⟨y, hy⟩ := exists_aug_eq ε hker (n + 1) _ hdH
    have hdy : dA (n + 1) y = 0 := by
      have hcomm : D.dV 0 (n + 1) (ε (n + 1) y)
          = ε (n + 2) (dA (n + 1) y) :=
        LinearMap.congr_fun (hεd (n + 1)) y
      refine hε (n + 2) ?_
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
      obtain ⟨bτ, hbτ⟩ := exists_dH_eq hrows P (n - P) _ (hdH (n - P) (by omega))
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

theorem stair_inj (hε : ∀ m, Function.Injective (ε m))
    (hεd : ∀ m, D.dV 0 m ∘ₗ ε m = ε (m + 1) ∘ₗ dA m)
    (hker : ∀ m, LinearMap.ker (D.dH 0 m) = LinearMap.range (ε m))
    (hrows : ∀ p m, LinearMap.ker (D.dH (p + 1) m) ≤ LinearMap.range (D.dH p m)) (n : ℕ) (y : A (n + 1))
    (bb : DoubleComplex.Tot D n)
    (hb : edge ε (n + 1) y = DoubleComplex.dTot D n bb) :
    ∃ y', y = dA n y' := by
  suffices H : ∀ P, ∀ bb : DoubleComplex.Tot D n,
      edge ε (n + 1) y = DoubleComplex.dTot D n bb →
      (∀ pp q h, P < pp → bb ⟨(pp, q), h⟩ = 0) →
      ∃ y', y = dA n y' from
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
    obtain ⟨w, hw⟩ := exists_aug_eq ε hker n _ hdH
    refine ⟨w, hε (n + 1) ?_⟩
    have h0 := congrFun hb ⟨(0, n + 1), by omega⟩
    rw [edge_apply_zero, DoubleComplex.dTot_apply_zero_succ] at h0
    have hcomm : D.dV 0 n (ε n w)
        = ε (n + 1) (dA n w) :=
      LinearMap.congr_fun (hεd n) w
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
      obtain ⟨bτ, hbτ⟩ := exists_dH_eq hrows P (n' - P) _ (hdH (n' - P) (by omega))
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

def Hedge (hεd : ∀ m, D.dV 0 m ∘ₗ ε m = ε (m + 1) ∘ₗ dA m)
    (hker : ∀ m, LinearMap.ker (D.dH 0 m) = LinearMap.range (ε m)) (n : ℕ) :
    (LinearMap.ker (dA (n + 1)) ⧸ (LinearMap.range (dA n)).comap (LinearMap.ker (dA (n + 1))).subtype) →ₗ[R] DoubleComplex.HTot D (n + 1) :=
  Submodule.mapQ _ _
    ((edge ε (n + 1)).restrict fun y hy => LinearMap.mem_ker.mpr <| by
      have hy' : dA (n + 1) y = 0 := LinearMap.mem_ker.mp hy
      have hch := LinearMap.congr_fun (edge_chain ε hεd hker (n + 1)) y
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hy', map_zero] at hch
      exact hch)
    (by
      rintro x ⟨y', hy'⟩
      refine ⟨edge ε n y', ?_⟩
      have hch := LinearMap.congr_fun (edge_chain ε hεd hker n) y'
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at hch
      exact hch.trans (congrArg _ hy'))

end Main

end P1SOL

end

open DoubleComplex P1SOL

theorem solution
    {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R)
    (A : ℕ → Type u) [∀ m, AddCommGroup (A m)] [∀ m, Module R (A m)]
    (dA : ∀ m, A m →ₗ[R] A (m + 1)) (ε : ∀ m, A m →ₗ[R] D.C 0 m)
    (hε : ∀ m, Function.Injective (ε m))
    (hεd : ∀ m, D.dV 0 m ∘ₗ ε m = ε (m + 1) ∘ₗ dA m)
    (hker : ∀ m, LinearMap.ker (D.dH 0 m) = LinearMap.range (ε m))
    (hrows : ∀ p m, LinearMap.ker (D.dH (p + 1) m) ≤ LinearMap.range (D.dH p m)) :
    (∃ e : LinearMap.ker (dA 0) ≃ₗ[R] DoubleComplex.HTot D 0,
        ∀ (a : A 0) (ha : a ∈ LinearMap.ker (dA 0)),
          ∃ hE : Pi.single (M := fun i : DoubleComplex.Diag 0 => D.C i.1.1 i.1.2) ⟨(0, 0), rfl⟩ (ε 0 a)
              ∈ LinearMap.ker (DoubleComplex.dTot D 0),
            e ⟨a, ha⟩ = Submodule.Quotient.mk ⟨_, hE⟩) ∧
      ∀ n : ℕ, ∃ e : (LinearMap.ker (dA (n + 1)) ⧸
            (LinearMap.range (dA n)).comap (LinearMap.ker (dA (n + 1))).subtype) ≃ₗ[R] DoubleComplex.HTot D (n + 1),
        ∀ (a : A (n + 1)) (ha : a ∈ LinearMap.ker (dA (n + 1))),
          ∃ hE : Pi.single (M := fun i : DoubleComplex.Diag (n + 1) => D.C i.1.1 i.1.2) ⟨(0, n + 1), by omega⟩ (ε (n + 1) a)
              ∈ LinearMap.ker (DoubleComplex.dTot D (n + 1)),
            e (Submodule.Quotient.mk ⟨a, ha⟩) = Submodule.Quotient.mk ⟨_, hE⟩ := by
  classical
  refine ⟨?_, fun n => ?_⟩
  ·
    let f : LinearMap.ker (dA 0) →ₗ[R] LinearMap.ker (DoubleComplex.dTot D 0) :=
      ((edge ε 0).comp (LinearMap.ker (dA 0)).subtype).codRestrict
        (LinearMap.ker (DoubleComplex.dTot D 0))
        fun y => LinearMap.mem_ker.mpr <| by
          have hch := LinearMap.congr_fun (edge_chain ε hεd hker 0) y.1
          rw [LinearMap.comp_apply, LinearMap.comp_apply] at hch
          exact hch.trans ((congrArg _ (LinearMap.mem_ker.mp y.2)).trans (map_zero _))
    have hf : Function.Bijective f := by
      refine ⟨fun y₁ y₂ hy => Subtype.ext (hε 0
          ((edge_apply_zero ε (Nat.zero_add 0) y₁.1).symm.trans
            ((congrFun (Subtype.ext_iff.mp hy) ⟨(0,0), Nat.zero_add 0⟩).trans
              (edge_apply_zero ε (Nat.zero_add 0) y₂.1)))),
       fun ⟨c, hc⟩ => ?_⟩
      have hdH : D.dH 0 0 (c ⟨(0,0), Nat.zero_add 0⟩) = 0 := by
        have h1 := congrFun (LinearMap.mem_ker.mp hc) ⟨(1, 0), rfl⟩
        rwa [Pi.zero_apply, DoubleComplex.dTot_apply_succ_zero] at h1
      obtain ⟨y, hy⟩ := exists_aug_eq ε hker 0 _ hdH
      have hdy : dA 0 y = 0 := by
        have hcomm : D.dV 0 0 (ε 0 y) = ε 1 (dA 0 y) := LinearMap.congr_fun (hεd 0) y
        refine hε 1 ?_
        rw [map_zero, ← hcomm, hy]
        have h0 := congrFun (LinearMap.mem_ker.mp hc) ⟨(0, 1), rfl⟩
        rwa [Pi.zero_apply, DoubleComplex.dTot_apply_zero_succ] at h0
      refine ⟨⟨y, LinearMap.mem_ker.mpr hdy⟩, Subtype.ext (funext fun ⟨⟨pp, q⟩, hpq⟩ => ?_)⟩
      obtain ⟨rfl, rfl⟩ : pp = 0 ∧ q = 0 := by omega
      exact (edge_apply_zero ε (Nat.zero_add 0) y).trans hy
    refine ⟨(LinearEquiv.ofBijective f hf).trans
        (Submodule.quotEquivOfEqBot (DoubleComplex.HTotB D 0) rfl).symm, fun a ha => ?_⟩
    exact ⟨(f ⟨a, ha⟩).2, rfl⟩
  ·
    refine ⟨LinearEquiv.ofBijective (Hedge ε hεd hker n)
      ⟨by
        rw [injective_iff_map_eq_zero]
        intro x hmap
        obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        simp only [Hedge, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hmap
        obtain ⟨bb, hbb⟩ := hmap
        obtain ⟨y', hy'⟩ := stair_inj ε hε hεd hker hrows n y bb hbb.symm
        exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y', hy'.symm⟩,
       fun x => by
        obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        obtain ⟨y, bb, hdy, hceq⟩ := stair_surj ε hε hεd hker hrows n c (LinearMap.mem_ker.mp hc)
        refine ⟨Submodule.Quotient.mk ⟨y, LinearMap.mem_ker.mpr hdy⟩, ?_⟩
        simp only [Hedge, Submodule.mapQ_apply, Submodule.Quotient.eq]
        exact ⟨-bb, by
          show DoubleComplex.dTot D n (-bb) = edge ε (n + 1) y - c
          rw [map_neg, hceq, sub_add_eq_sub_sub, sub_self, zero_sub]⟩⟩, fun a ha => ?_⟩
    have hE : edge ε (n + 1) a ∈ LinearMap.ker (DoubleComplex.dTot D (n + 1)) := by
      rw [LinearMap.mem_ker]
      have hch := LinearMap.congr_fun (edge_chain ε hεd hker (n + 1)) a
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.mem_ker.mp ha, map_zero] at hch
      exact hch
    exact ⟨hE, rfl⟩

end S_DoubleComplex_exists_HTot_equiv_mk_eq_mk_single_of_rows_exact_of_augmentation
end P2MW
export P2MW.S_DoubleComplex_exists_HTot_equiv_mk_eq_mk_single_of_rows_exact_of_augmentation (solution)
