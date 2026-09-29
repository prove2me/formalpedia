-- Prove2me | solution 1 for DoubleComplex.boundedSpectralSequence
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/bd008358-6bff-5d96-99e7-a92db8d7ab1a

import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DoubleComplex_boundedSpectralSequence

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u

noncomputable section

namespace DoubleComplex
p2m_export "DoubleComplex" "Bounded Diag Tot dTot HTotB HTot dTot_apply_zero_succ dTot_apply_succ_zero dTot_apply_succ_succ dTot_comp_dTot colB colH colHdH E₂IB E₂I SubQuot Convergence BoundedSpectralSequence"
p2m_open "DoubleComplex"

def leOfSubsingleton (R : Type u) [CommRing R]
    (M N : Type u) [AddCommGroup M] [Module R M] [Subsingleton M]
    [AddCommGroup N] [Module R N] [Subsingleton N] : M ≃ₗ[R] N where
  toFun _ := 0
  invFun _ := 0
  map_add' _ _ := Subsingleton.elim _ _
  map_smul' _ _ := Subsingleton.elim _ _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

section FilTot

variable {R : Type u} [CommRing R] (D : Bounded R)

def FilTot (p n : ℕ) : Submodule R (Tot D n) :=
  ⨅ (i : Diag n) (_ : i.1.1 < p),
    LinearMap.ker (LinearMap.proj (R := R)
      (φ := fun j : Diag n => D.C j.1.1 j.1.2) i)

theorem mem_FilTot {p n : ℕ} (c : Tot D n) :
    c ∈ FilTot D p n ↔ ∀ i : Diag n, i.1.1 < p → c i = 0 := by
  simp only [FilTot, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.proj_apply]

theorem FilTot_antitone (n : ℕ) : Antitone (fun p => FilTot D p n) := by
  intro p p' hpp'
  simp only [SetLike.le_def, mem_FilTot]
  intro c hc i hi
  exact hc i (lt_of_lt_of_le hi hpp')

theorem FilTot_zero (n : ℕ) : FilTot D 0 n = ⊤ := by
  simp only [FilTot, Nat.not_lt_zero, iInf_false, iInf_top]

theorem FilTot_top (n : ℕ) : FilTot D (n + 1) n = ⊥ := by
  refine le_antisymm (fun c hc => ?_) bot_le
  rw [mem_FilTot] at hc
  refine Submodule.mem_bot R |>.mpr (funext fun i => hc i ?_)
  have h := i.2; omega

theorem FilTot_N_subsingleton (n : ℕ) (c : Tot D n)
    (hc : c ∈ FilTot D D.N n) (i : Diag n) : c i = 0 := by
  rcases Nat.lt_or_ge i.1.1 D.N with h | h
  · exact (mem_FilTot D c).mp hc i h
  · exact @Subsingleton.elim _ (D.hBound i.1.1 i.1.2 (Or.inl h)) _ _

theorem FilTot_N (n : ℕ) : FilTot D D.N n = ⊥ := by
  refine le_antisymm (fun c hc => ?_) bot_le
  exact Submodule.mem_bot R |>.mpr (funext fun i => FilTot_N_subsingleton D n c hc i)

theorem dTot_FilTot_le (p n : ℕ) :
    (FilTot D p n).map (dTot D n)
      ≤ FilTot D p (n + 1) := by
  refine Submodule.map_le_iff_le_comap.mpr fun c hc => ?_
  rw [mem_FilTot] at hc
  simp only [Submodule.mem_comap, mem_FilTot]
  intro i hpp
  obtain ⟨⟨pp, q⟩, h⟩ := i
  change pp < p at hpp
  match pp, q, h, hpp with
  | 0, q' + 1, h, hpp =>
    rw [dTot_apply_zero_succ, hc ⟨(0, q'), by omega⟩ hpp, map_zero]
  | p' + 1, 0, h, hpp =>
    have hlt : p' < p := Nat.lt_of_succ_lt hpp
    rw [dTot_apply_succ_zero, hc ⟨(p', 0), by omega⟩ hlt, map_zero]
  | p' + 1, q' + 1, h, hpp =>
    have hlt : p' < p := Nat.lt_of_succ_lt hpp
    rw [dTot_apply_succ_succ, hc ⟨(p', q' + 1), by omega⟩ hlt,
      hc ⟨(p' + 1, q'), by omega⟩ hpp, map_zero, map_zero, smul_zero, add_zero]

end FilTot

section Edge

variable {R : Type u} [CommRing R] (D : Bounded R)

abbrev edgeSlot (p : ℕ) : Diag p := ⟨(p, 0), by omega⟩

theorem ne_edgeSlot_of_lt {p : ℕ} (i : Diag p)
    (hi : i.1.1 < p) : i ≠ edgeSlot p := by
  intro heq; rw [heq] at hi; exact lt_irrefl p hi

theorem Diag_col_lt_of_ne {p : ℕ} (i : Diag p)
    (hi : i ≠ edgeSlot p) : i.1.1 < p := by
  obtain ⟨⟨a, b⟩, h⟩ := i
  rcases Nat.lt_or_ge a p with hlt | hge
  · exact hlt
  · obtain rfl : a = p := by omega
    obtain rfl : b = 0 := by omega
    exact absurd (Subtype.ext rfl) hi

abbrev edgeSingle (p : ℕ) (x : D.C p 0) : Tot D p :=
  Pi.single (M := fun j : Diag p => D.C j.1.1 j.1.2)
    (edgeSlot p) x

theorem edgeSingle_mem_FilTot (p : ℕ) (x : D.C p 0) :
    edgeSingle D p x ∈ FilTot D p p := by
  refine (mem_FilTot D _).mpr fun i hi => ?_
  exact Pi.single_eq_of_ne (M := fun j : Diag p => D.C j.1.1 j.1.2)
    (ne_edgeSlot_of_lt i hi) x

def edgeProj (p : ℕ) : ↥(FilTot D p p) ≃ₗ[R] D.C p 0 where
  toFun c := c.1 (edgeSlot p)
  invFun x := ⟨edgeSingle D p x, edgeSingle_mem_FilTot D p x⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv c := by
    refine Subtype.ext (funext fun i => ?_)
    show edgeSingle D p (c.1 (edgeSlot p)) i = c.1 i
    rcases eq_or_ne i (edgeSlot p) with rfl | hi
    · exact Pi.single_eq_same _ _
    · rw [show edgeSingle D p (c.1 (edgeSlot p)) i = 0 from
          Pi.single_eq_of_ne (M := fun j : Diag p => D.C j.1.1 j.1.2) hi _,
        (mem_FilTot D _).mp c.2 i (Diag_col_lt_of_ne i hi)]
  right_inv x := Pi.single_eq_same _ _

theorem neg_one_pow_zsmul_eq_zero {M : Type*} [AddCommGroup M] (n : ℕ) (x : M) :
    ((-1 : ℤ) ^ n) • x = 0 ↔ x = 0 := by
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow, one_smul]
  · rw [ho.neg_one_pow, neg_one_smul, neg_eq_zero]

theorem edge_ker_fwd (p : ℕ) (c : Tot D p)
    (hcF : c ∈ FilTot D p p)
    (hker : c ∈ LinearMap.ker (dTot D p)) :
    c (edgeSlot p) ∈ LinearMap.ker (D.dH p 0) ⊓ LinearMap.ker (D.dV p 0) := by
  have hc := (mem_FilTot D _).mp hcF
  refine ⟨?_, ?_⟩
  · have := congrFun (LinearMap.mem_ker.mp hker) ⟨(p + 1, 0), by omega⟩
    rwa [dTot_apply_succ_zero, Pi.zero_apply] at this
  · rcases p with _ | p'
    · have := congrFun (LinearMap.mem_ker.mp hker) ⟨(0, 1), by omega⟩
      rwa [dTot_apply_zero_succ, Pi.zero_apply] at this
    · have h1 : (p' : ℕ) < p' + 1 := Nat.lt_succ_self p'
      have := congrFun (LinearMap.mem_ker.mp hker) ⟨(p' + 1, 1), by omega⟩
      rw [dTot_apply_succ_succ, hc ⟨(p', 1), by omega⟩ h1, map_zero,
        zero_add, Pi.zero_apply] at this
      exact LinearMap.mem_ker.mpr
        ((neg_one_pow_zsmul_eq_zero (p' + 1) _).mp this)

theorem edge_ker_rev (p : ℕ) (x : D.C p 0)
    (hH : x ∈ LinearMap.ker (D.dH p 0)) (hV : x ∈ LinearMap.ker (D.dV p 0)) :
    edgeSingle D p x ∈ LinearMap.ker (dTot D p) := by
  have hc := (mem_FilTot D _).mp (edgeSingle_mem_FilTot D p x)
  refine LinearMap.mem_ker.mpr (funext fun i => ?_)
  obtain ⟨⟨pp, q⟩, h⟩ := i
  show dTot D p (edgeSingle D p x) ⟨(pp, q), h⟩ = 0
  match pp, q, h with
  | 0, q' + 1, h =>
    rcases p with _ | p'
    · obtain rfl : q' = 0 := by omega
      rw [dTot_apply_zero_succ]
      simpa only [edgeSingle, Pi.single_eq_same] using LinearMap.mem_ker.mp hV
    · have h0 : (0 : ℕ) < p' + 1 := Nat.succ_pos p'
      rw [dTot_apply_zero_succ, hc ⟨(0, q'), by omega⟩ h0, map_zero]
  | pp' + 1, 0, h =>
    obtain rfl : pp' = p := by omega
    rw [dTot_apply_succ_zero]
    simpa only [edgeSingle, Pi.single_eq_same] using LinearMap.mem_ker.mp hH
  | pp' + 1, q' + 1, h =>
    rw [dTot_apply_succ_succ]
    have hlt : (pp' : ℕ) < p := by omega
    rcases Nat.lt_or_eq_of_le (by omega : pp' + 1 ≤ p) with hlt' | heq
    · rw [hc ⟨(pp', q' + 1), by omega⟩ hlt, hc ⟨(pp' + 1, q'), by omega⟩ hlt',
        map_zero, map_zero, smul_zero, add_zero]
    · subst heq
      obtain rfl : q' = 0 := by omega
      have hVx : D.dV (pp' + 1) 0
          (edgeSingle D (pp' + 1) x ⟨(pp' + 1, 0), by omega⟩) = 0 := by
        simpa only [edgeSingle, Pi.single_eq_same] using LinearMap.mem_ker.mp hV
      simp only [hc ⟨(pp', 1), by omega⟩ hlt, map_zero, hVx, smul_zero, add_zero]

end Edge

section KerHV

variable {R : Type u} [CommRing R] (D : Bounded R)

abbrev KerHV (p : ℕ) : Submodule R (D.C p 0) :=
  LinearMap.ker (D.dH p 0) ⊓ LinearMap.ker (D.dV p 0)

def FilH (p n : ℕ) : Submodule R (HTot D n) :=
  Submodule.map (HTotB D n).mkQ
    ((FilTot D p n).comap (LinearMap.ker (dTot D n)).subtype)

theorem FilH_zero (n : ℕ) : FilH D 0 n = ⊤ := by
  rw [FilH, FilTot_zero, Submodule.comap_top, Submodule.map_top,
    Submodule.range_mkQ]

theorem FilH_top (n : ℕ) : FilH D (n + 1) n = ⊥ := by
  rw [FilH, FilTot_top, Submodule.comap_bot,
    Submodule.ker_subtype, Submodule.map_bot]

def colH0_equiv (p : ℕ) :
    colH D p 0 ≃ₗ[R] ↥(LinearMap.ker (D.dV p 0)) :=
  Submodule.quotEquivOfEqBot _ rfl

def toColH (p : ℕ) :
    ↥(KerHV D p) →ₗ[R] colH D p 0 :=
  (colB D p 0).mkQ ∘ₗ
    Submodule.inclusion (inf_le_right : KerHV D p ≤ LinearMap.ker (D.dV p 0))

theorem KerHV_le_ker_colHdH (p : ℕ) (x : ↥(KerHV D p)) :
    toColH D p x ∈ LinearMap.ker (colHdH D p 0) := by
  refine LinearMap.mem_ker.mpr ?_
  show Submodule.mapQ _ _ _ _ (Submodule.Quotient.mk _) = 0
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.mem_bot R |>.mpr (Subtype.ext (LinearMap.mem_ker.mp x.2.1))

def toE₂ (p : ℕ) :
    ↥(KerHV D p) →ₗ[R] E₂I D p 0 :=
  (E₂IB D p 0).mkQ ∘ₗ
    LinearMap.codRestrict (LinearMap.ker (colHdH D p 0))
      (toColH D p) (KerHV_le_ker_colHdH D p)

theorem toE₂_surjective (p : ℕ) :
    Function.Surjective (toE₂ D p) := by
  refine (Submodule.mkQ_surjective _).comp fun z => ?_

  set y := colH0_equiv D p z.1 with hy
  have hz : (colB D p 0).mkQ y = z.1 := by
    rw [show (colB D p 0).mkQ y
        = (colH0_equiv D p).symm y from rfl,
      hy, LinearEquiv.symm_apply_apply]
  have hyH : y.1 ∈ LinearMap.ker (D.dH p 0) := by

    have hker : colHdH D p 0 ((colB D p 0).mkQ y) = 0 :=
      hz ▸ LinearMap.mem_ker.mp z.2
    have hker' := congrArg (colH0_equiv D (p + 1)) hker
    simp only [map_zero] at hker'
    exact LinearMap.mem_ker.mpr (congrArg Subtype.val hker')
  exact ⟨⟨y.1, hyH, y.2⟩, Subtype.ext hz⟩

end KerHV

section ZigZag

variable {R : Type u} [CommRing R] (D : Bounded R)

def zigTarget (p : ℕ) : Submodule R (Tot D p) :=
  (FilTot D (p + 1) (p + 1)).comap (dTot D p)

def A (r p : ℕ) : Submodule R (Tot D p) :=
  FilTot D (p + 1 - r) p ⊓ zigTarget D p

theorem A_mono (p : ℕ) : Monotone fun r => A D r p := by
  intro r r' hrr'
  exact inf_le_inf_right _ (FilTot_antitone D p (by omega))

theorem A_zero (p : ℕ) : A D 0 p = ⊥ := by
  rw [A, Nat.sub_zero, FilTot_top, bot_inf_eq]

theorem A_full (p : ℕ) : A D (p + 1) p = zigTarget D p := by
  rw [A, Nat.sub_self, FilTot_zero, top_inf_eq]

def zigOut (p : ℕ) : Tot D p →ₗ[R] D.C (p + 1) 0 :=
  LinearMap.proj (R := R)
      (φ := fun j : Diag (p + 1) => D.C j.1.1 j.1.2)
      (edgeSlot (p + 1)) ∘ₗ
    dTot D p

theorem zigOut_apply (p : ℕ) (b : Tot D p) :
    zigOut D p b = D.dH p 0 (b (edgeSlot p)) := by
  show dTot D p b ⟨(p + 1, 0), by omega⟩ = _
  rw [dTot_apply_succ_zero]

theorem dTot_eq_edgeSingle_zigOut (p : ℕ) (b : Tot D p)
    (hb : b ∈ zigTarget D p) :
    dTot D p b
      = edgeSingle D (p + 1) (zigOut D p b) := by
  have hbF : dTot D p b ∈ FilTot D (p + 1) (p + 1) := hb
  exact congrArg Subtype.val ((edgeProj D (p + 1)).left_inv ⟨_, hbF⟩).symm

theorem zigOut_mem_KerHV (p : ℕ) (b : Tot D p)
    (hb : b ∈ zigTarget D p) :
    zigOut D p b ∈ KerHV D (p + 1) := by
  have hker : dTot D p b ∈ LinearMap.ker (dTot D (p + 1)) :=
    LinearMap.mem_ker.mpr (LinearMap.congr_fun (dTot_comp_dTot D p) b)
  have := edge_ker_fwd D (p + 1) _ hb hker
  rwa [show (dTot D p b) (edgeSlot (p + 1))
    = zigOut D p b from rfl] at this

def B (r p : ℕ) : Submodule R (E₂I D (p + 1) 0) :=
  Submodule.map
    ((toE₂ D (p + 1)) ∘ₗ
      LinearMap.codRestrict (KerHV D (p + 1))
        ((zigOut D p).comp (zigTarget D p).subtype)
        (fun b => zigOut_mem_KerHV D p b.1 b.2))
    ((A D r p).comap (zigTarget D p).subtype)

theorem B_mono (p : ℕ) : Monotone fun r => B D r p := fun _ _ h =>
  Submodule.map_mono (Submodule.comap_mono (A_mono D p h))

theorem B_zero (p : ℕ) : B D 0 p = ⊥ := by
  rw [B, A_zero, Submodule.comap_bot, Submodule.ker_subtype,
    Submodule.map_bot]

theorem A_inter_FilTot (r p : ℕ) (hr : 1 ≤ r) :
    A D r p ⊓ FilTot D (p + 2 - r) p = A D (r - 1) p := by
  unfold A
  rw [inf_right_comm, inf_eq_right.mpr
      (FilTot_antitone D p (by omega : p + 1 - r ≤ p + 2 - r)),
    show p + 1 - (r - 1) = p + 2 - r from by omega]

theorem θ_mem_ker_dV (p a q : ℕ) (haq : a + q = p) (ha : a ≤ p - q)
    (b : Tot D p) (hbF : b ∈ FilTot D a p)
    (hbT : b ∈ zigTarget D p) :
    D.dV a q (b ⟨(a, q), haq⟩) = 0 := by
  have hF := (mem_FilTot D _).mp hbF
  have hT := (mem_FilTot D _).mp (Submodule.mem_comap.mp hbT)
  match a, haq, hF with
  | 0, haq, hF =>
    have h0 : dTot D p b ⟨(0, q + 1), by omega⟩ = 0 :=
      hT ⟨(0, q + 1), by omega⟩ p.succ_pos
    rwa [dTot_apply_zero_succ] at h0
  | a' + 1, haq, hF =>
    have hlt1 : (a' + 1 : ℕ) < p + 1 := by omega
    have h0 : dTot D p b ⟨(a' + 1, q + 1), by omega⟩ = 0 :=
      hT ⟨(a' + 1, q + 1), by omega⟩ hlt1
    have hFlt : (a' : ℕ) < a' + 1 := Nat.lt_succ_self a'
    rw [dTot_apply_succ_succ, hF ⟨(a', q + 1), by omega⟩ hFlt,
      map_zero, zero_add] at h0
    exact (neg_one_pow_zsmul_eq_zero (a' + 1) _).mp h0

theorem toE₂_dH_kerV (p : ℕ) (y : D.C p 0) (hy : y ∈ LinearMap.ker (D.dV p 0)) :
    toE₂ D (p + 1)
      ⟨D.dH p 0 y, LinearMap.mem_ker.mpr (LinearMap.congr_fun (D.dH_sq p 0) y),
        LinearMap.mem_ker.mpr (by
          rw [← LinearMap.comp_apply, D.dHV_comm, LinearMap.comp_apply,
            LinearMap.mem_ker.mp hy, map_zero])⟩ = 0 := by
  refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
  refine Submodule.mem_comap.mpr ⟨(colB D p 0).mkQ ⟨y, hy⟩, ?_⟩

  simp only [Submodule.coe_subtype, LinearMap.codRestrict_apply]
  exact congrArg (colB D (p + 1) 0).mkQ (Subtype.ext rfl)

theorem B_one (p : ℕ) : B D 1 p = ⊥ := by
  refine le_antisymm (fun z hz => ?_) bot_le
  simp only [B, Submodule.mem_map, Submodule.mem_comap] at hz
  obtain ⟨⟨b, hbT⟩, hbA, rfl⟩ := hz

  have hbV : D.dV p 0 (b (edgeSlot p)) = 0 :=
    θ_mem_ker_dV D p p 0 (by omega) (by omega) b hbA.1 hbA.2
  refine (Submodule.mem_bot R).mpr ?_
  have hgoal := toE₂_dH_kerV D p _ (LinearMap.mem_ker.mpr hbV)
  refine Eq.trans ?_ hgoal
  exact congrArg (toE₂ D (p + 1))
    (Subtype.ext (zigOut_apply D p b))

theorem zigzag_dH (p a q' : ℕ) (haq : a + (q' + 1) = p)
    (b : Tot D p) (hbT : b ∈ zigTarget D p) :
    D.dH a (q' + 1) (b ⟨(a, q' + 1), haq⟩)
      = ((-1 : ℤ) ^ a) • D.dV (a + 1) q' (b ⟨(a + 1, q'), by omega⟩) := by
  have hT := (mem_FilTot D _).mp (Submodule.mem_comap.mp hbT)
  have hlt1 : (a + 1 : ℕ) < p + 1 := by omega
  have h0 : dTot D p b ⟨(a + 1, q' + 1), by omega⟩ = 0 :=
    hT ⟨(a + 1, q' + 1), by omega⟩ hlt1
  rw [dTot_apply_succ_succ] at h0
  have hres := eq_neg_of_add_eq_zero_left h0
  rwa [← neg_one_smul ℤ ((_ : ℤ)^_ • _), smul_smul,
    show (-1 : ℤ) * (-1)^(a+1) = (-1)^a from by ring] at hres

theorem θ_dH_mem_colB (p a q' : ℕ) (haq : a + (q' + 1) = p)
    (b : Tot D p) (hbT : b ∈ zigTarget D p)
    (hbV : D.dV a (q' + 1) (b ⟨(a, q' + 1), haq⟩) = 0) :
    (⟨D.dH a (q' + 1) (b ⟨(a, q' + 1), haq⟩), LinearMap.mem_ker.mpr (by
        rw [← LinearMap.comp_apply, D.dHV_comm, LinearMap.comp_apply, hbV, map_zero])⟩
      : ↥(LinearMap.ker (D.dV (a + 1) (q' + 1))))
        ∈ colB D (a + 1) (q' + 1) := by
  refine Submodule.mem_comap.mpr ?_
  simp only [Submodule.coe_subtype, LinearMap.mem_range]
  exact ⟨((-1 : ℤ) ^ a) • b ⟨(a + 1, q'), by omega⟩, by
    rw [map_zsmul, ← zigzag_dH D p a q' haq b hbT]⟩

abbrev η (p : ℕ) :
    ↥(zigTarget D p) →ₗ[R] E₂I D (p + 1) 0 :=
  (toE₂ D (p + 1)) ∘ₗ
    LinearMap.codRestrict (KerHV D (p + 1))
      ((zigOut D p).comp (zigTarget D p).subtype)
      (fun b => zigOut_mem_KerHV D p b.1 b.2)

abbrev totSingle {n : ℕ} (i : Diag n)
    (v : D.C i.1.1 i.1.2) : Tot D n :=
  Pi.single (M := fun j : Diag n => D.C j.1.1 j.1.2) i v

theorem totSingle_mem_FilTot {n : ℕ} (i : Diag n)
    (v : D.C i.1.1 i.1.2) : totSingle D i v ∈ FilTot D i.1.1 n := by
  refine (mem_FilTot D _).mpr fun j hj => ?_
  refine Pi.single_eq_of_ne (M := fun j : Diag n => D.C j.1.1 j.1.2) ?_ v
  intro heq; rw [heq] at hj; exact lt_irrefl _ hj

theorem dTot_totSingle_col_same {n a q : ℕ} (haq : a + q = n) (v : D.C a q) :
    dTot D n (totSingle D ⟨(a, q), haq⟩ v) ⟨(a, q + 1), by omega⟩
      = ((-1 : ℤ) ^ a) • D.dV a q v := by
  match a, haq with
  | 0, haq =>
    rw [dTot_apply_zero_succ, pow_zero, one_smul]
    exact congrArg _ (Pi.single_eq_same _ _)
  | a' + 1, haq =>
    rw [dTot_apply_succ_succ,
      show totSingle D ⟨(a' + 1, q), haq⟩ v ⟨(a', q + 1), by omega⟩ = 0 from
        Pi.single_eq_of_ne (M := fun j : Diag n => D.C j.1.1 j.1.2)
          (fun h => by injection (congrArg Subtype.val h) with h1; omega) _,
      map_zero, zero_add]
    exact congrArg _ (congrArg _ (Pi.single_eq_same _ _))

theorem dTot_totSingle_col_succ {n a q : ℕ} (haq : a + q = n) (v : D.C a q) :
    dTot D n (totSingle D ⟨(a, q), haq⟩ v) ⟨(a + 1, q), by omega⟩
      = D.dH a q v := by
  match q, haq with
  | 0, haq =>
    rw [dTot_apply_succ_zero]
    exact congrArg _ (Pi.single_eq_same _ _)
  | q'' + 1, haq =>
    rw [dTot_apply_succ_succ,
      show totSingle D ⟨(a, q'' + 1), haq⟩ v ⟨(a + 1, q''), by omega⟩ = 0 from
        Pi.single_eq_of_ne (M := fun j : Diag n => D.C j.1.1 j.1.2)
          (fun h => by injection (congrArg Subtype.val h) with h1; omega) _,
      map_zero, smul_zero, add_zero]
    exact congrArg _ (Pi.single_eq_same _ _)

theorem sub_dTot_mem_zigTarget (p' : ℕ) (b : Tot D (p' + 1))
    (hbT : b ∈ zigTarget D (p' + 1)) (w : Tot D p') :
    b - dTot D p' w ∈ zigTarget D (p' + 1) := by
  refine Submodule.mem_comap.mpr ?_
  rw [map_sub, show dTot D (p' + 1) (dTot D p' w) = 0 from
    LinearMap.congr_fun (dTot_comp_dTot D p') w, sub_zero]
  exact hbT

theorem zigOut_sub_dTot (p' : ℕ) (b : Tot D (p' + 1))
    (w : Tot D p') :
    zigOut D (p' + 1) (b - dTot D p' w)
      = zigOut D (p' + 1) b := by
  rw [map_sub, sub_eq_self]
  show dTot D (p' + 1) (dTot D p' w)
    (edgeSlot (p' + 1 + 1)) = 0
  rw [← LinearMap.comp_apply, dTot_comp_dTot]; rfl

theorem mem_FilTot_succ_iff {p a q : ℕ} (haq : a + q = p)
    (c : Tot D p) :
    c ∈ FilTot D (a + 1) p
      ↔ c ∈ FilTot D a p ∧ c ⟨(a, q), haq⟩ = 0 := by
  simp only [mem_FilTot]
  refine ⟨fun h => ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h ⟨(a, q), haq⟩ (Nat.lt_succ_self a)⟩,
    fun ⟨hF, h0⟩ i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
  · exact hF i hlt
  · obtain ⟨⟨a', q'⟩, haq'⟩ := i
    obtain rfl : a' = a := heq
    obtain rfl : q' = q := by omega
    exact h0

def ψ₁ (p a q' : ℕ) (haq : a + (q' + 1) = p) :
    ↥(FilTot D a p ⊓ zigTarget D p)
      →ₗ[R] ↥(LinearMap.ker (D.dV a (q' + 1))) :=
  LinearMap.codRestrict _
    ((LinearMap.proj (R := R)
        (φ := fun j : Diag p => D.C j.1.1 j.1.2) ⟨(a, q' + 1), haq⟩).comp
      (FilTot D a p ⊓ zigTarget D p).subtype)
    (fun b => LinearMap.mem_ker.mpr
      (θ_mem_ker_dV D p a (q' + 1) haq
        (le_of_eq (by omega : a = p - (q' + 1))) b.1 b.2.1 b.2.2))

def ψ (p a q' : ℕ) (haq : a + (q' + 1) = p) :
    ↥(FilTot D a p ⊓ zigTarget D p)
      →ₗ[R] E₂I D a (q' + 1) :=
  (E₂IB D a (q' + 1)).mkQ ∘ₗ
    LinearMap.codRestrict (LinearMap.ker (colHdH D a (q' + 1)))
      ((colB D a (q' + 1)).mkQ ∘ₗ ψ₁ D p a q' haq)
      (fun b => by
        refine LinearMap.mem_ker.mpr ?_
        show Submodule.mapQ _ _ _ _ (Submodule.Quotient.mk _) = 0
        rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
        exact θ_dH_mem_colB D p a q' haq b.1 b.2.2
          (LinearMap.mem_ker.mp (ψ₁ D p a q' haq b).2))

theorem ψ_eq_zero_iff (p a q' : ℕ) (haq : a + (q' + 1) = p)
    (b : ↥(FilTot D a p ⊓ zigTarget D p)) :
    ψ D p a q' haq b = 0
      ↔ (⟨(colB D a (q' + 1)).mkQ (ψ₁ D p a q' haq b), by
            refine LinearMap.mem_ker.mpr ?_
            show Submodule.mapQ _ _ _ _ (Submodule.Quotient.mk _) = 0
            rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
            exact θ_dH_mem_colB D p a q' haq b.1 b.2.2
              (LinearMap.mem_ker.mp (ψ₁ D p a q' haq b).2)⟩
          : ↥(LinearMap.ker (colHdH D a (q' + 1))))
        ∈ E₂IB D a (q' + 1) := by
  exact Submodule.Quotient.mk_eq_zero _

theorem η_mem_B_of_zigOut_eq (p a q' : ℕ) (haq : a + (q' + 1) = p)
    (bT : ↥(zigTarget D p)) (c : Tot D p)
    (hcF : c ∈ FilTot D (a + 1) p) (hcT : c ∈ zigTarget D p)
    (hcO : zigOut D p c = zigOut D p bT.1) :
    η D p bT ∈ B D (q' + 1) p := by
  refine ⟨⟨c, hcT⟩, Submodule.mem_comap.mpr ⟨?_, hcT⟩,
    congrArg (toE₂ D (p + 1)) (Subtype.ext hcO)⟩
  exact (show p + 1 - (q' + 1) = a + 1 from by omega) ▸ hcF

theorem core_mem_B_pred (p a q' : ℕ) (haq : a + (q' + 1) = p)
    (b : ↥(FilTot D a p ⊓ zigTarget D p))
    (hψ0 : ψ D p a q' haq b = 0) :
    η D p ⟨b.1, b.2.2⟩ ∈ B D (q' + 1) p := by

  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  have haq' : a + q' = p' := by omega

  match a, haq, haq', b, hψ0 with
  | 0, haq, haq', b, hψ0 =>

    have hψ0' := (ψ_eq_zero_iff D (p' + 1) 0 q' haq b).mp hψ0
    have hcolB : ψ₁ D (p' + 1) 0 q' haq b ∈ colB D 0 (q' + 1) :=
      (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val ((Submodule.mem_bot R).mp hψ0'))
    obtain ⟨z', hz'⟩ := hcolB

    let w : Tot D p' := totSingle D ⟨(0, q'), haq'⟩ z'
    refine η_mem_B_of_zigOut_eq D (p' + 1) 0 q' haq ⟨b.1, b.2.2⟩
      (b.1 - dTot D p' w) ?_
      (sub_dTot_mem_zigTarget D p' b.1 b.2.2 w)
      (zigOut_sub_dTot D p' b.1 w)

    refine (mem_FilTot_succ_iff D haq _).mpr
      ⟨(mem_FilTot D _).mpr fun i hi => absurd hi (Nat.not_lt_zero _), ?_⟩
    have hdTw : dTot D p' w ⟨(0, q' + 1), by omega⟩
        = b.1 ⟨(0, q' + 1), haq⟩ := by
      rw [dTot_totSingle_col_same D haq' z', pow_zero, one_smul]; exact hz'
    exact sub_eq_zero.mpr hdTw.symm
  | a'' + 1, haq, haq', b, hψ0 =>

    have hψ0' := (ψ_eq_zero_iff D (p' + 1) (a'' + 1) q' haq b).mp hψ0
    obtain ⟨wc, hwc⟩ := hψ0'
    obtain ⟨y', rfl⟩ := (colB D a'' (q' + 1)).mkQ_surjective wc

    have hxdH : ψ₁ D (p' + 1) (a'' + 1) q' haq b
          - (D.dH a'' (q' + 1)).restrict
              (fun v hv => LinearMap.mem_ker.mpr (by
                rw [← LinearMap.comp_apply, D.dHV_comm, LinearMap.comp_apply,
                  LinearMap.mem_ker.mp hv, map_zero])) y'
        ∈ colB D (a'' + 1) (q' + 1) := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero]
      exact hwc.symm
    obtain ⟨z', hz'⟩ := hxdH
    have hz'' : D.dV (a'' + 1) q' z'
        = b.1 ⟨(a'' + 1, q' + 1), haq⟩ - D.dH a'' (q' + 1) y'.1 := hz'

    let w₁ : Tot D p' :=
      totSingle D ⟨(a'' + 1, q'), haq'⟩ (((-1 : ℤ) ^ (a'' + 1)) • z')
    set b' := b.1 - dTot D p' w₁ with hb'_def
    have hb'T : b' ∈ zigTarget D (p' + 1) :=
      sub_dTot_mem_zigTarget D p' b.1 b.2.2 w₁
    have hb'F : b' ∈ FilTot D (a'' + 1) (p' + 1) := by
      refine Submodule.sub_mem _ b.2.1 ?_
      exact dTot_FilTot_le D (a'' + 1) p'
        ⟨w₁, totSingle_mem_FilTot D ⟨(a'' + 1, q'), haq'⟩ _, rfl⟩
    have hb'slot : b' ⟨(a'' + 1, q' + 1), haq⟩ = D.dH a'' (q' + 1) y'.1 := by
      have hdTw₁ : dTot D p' w₁ ⟨(a'' + 1, q' + 1), by omega⟩
          = b.1 ⟨(a'' + 1, q' + 1), haq⟩ - D.dH a'' (q' + 1) y'.1 := by
        rw [dTot_totSingle_col_same D haq' _, map_zsmul, smul_smul, ← pow_add,
          show ((-1 : ℤ) ^ (a'' + 1 + (a'' + 1))) = 1 from
            Even.neg_one_pow ⟨a'' + 1, rfl⟩, one_smul, hz'']
      show b.1 ⟨(a'' + 1, q' + 1), haq⟩
          - dTot D p' w₁ ⟨(a'' + 1, q' + 1), haq⟩ = _
      rw [hdTw₁, sub_sub_cancel]

    have haq2 : a'' + (q' + 1) = p' := by omega
    have haq3 : a'' + (q' + 2) = p' + 1 := by omega
    let w₂ : Tot D p' :=
      totSingle D ⟨(a'', q' + 1), haq2⟩ y'.1
    refine η_mem_B_of_zigOut_eq D (p' + 1) (a'' + 1) q' haq ⟨b.1, b.2.2⟩
      (b' - dTot D p' w₂) ?_
      (sub_dTot_mem_zigTarget D p' b' hb'T w₂)
      ((zigOut_sub_dTot D p' b' w₂).trans
        (zigOut_sub_dTot D p' b.1 w₁))

    refine (mem_FilTot_succ_iff D haq _).mpr ⟨?_, ?_⟩
    ·

      refine (mem_FilTot_succ_iff D haq3 _).mpr ⟨?_, ?_⟩
      · refine Submodule.sub_mem _
          (FilTot_antitone D (p' + 1) (Nat.le_succ a'') hb'F) ?_
        exact dTot_FilTot_le D a'' p'
          ⟨w₂, totSingle_mem_FilTot D ⟨(a'', q' + 1), haq2⟩ _, rfl⟩
      ·

        have hb'0 : b' ⟨(a'', q' + 2), haq3⟩ = 0 :=
          (mem_FilTot D _).mp hb'F ⟨(a'', q' + 2), haq3⟩ (Nat.lt_succ_self a'')
        show b' ⟨(a'', q' + 2), haq3⟩
            - dTot D p' w₂ ⟨(a'', q' + 2), haq3⟩ = 0
        rw [hb'0, dTot_totSingle_col_same D haq2 y'.1,
          LinearMap.mem_ker.mp y'.2, smul_zero, sub_self]
    ·
      show b' ⟨(a'' + 1, q' + 1), haq⟩
          - dTot D p' w₂ ⟨(a'' + 1, q' + 1), haq⟩ = 0
      rw [hb'slot, dTot_totSingle_col_succ D haq2 y'.1, sub_self]

def φ (p a q' : ℕ) (haq : a + (q' + 1) = p) :
    ↥(FilTot D a p ⊓ zigTarget D p) →ₗ[R]
      ↥(B D (q' + 2) p)
        ⧸ (B D (q' + 1) p).comap (B D (q' + 2) p).subtype :=
  Submodule.mkQ _ ∘ₗ
    LinearMap.codRestrict (B D (q' + 2) p)
      ((η D p).comp
        (Submodule.inclusion (inf_le_right :
          FilTot D a p ⊓ zigTarget D p ≤ zigTarget D p)))
      (fun b => ⟨⟨b.1, b.2.2⟩, Submodule.mem_comap.mpr
        ⟨(show p + 1 - (q' + 2) = a from by omega) ▸ b.2.1, b.2.2⟩, rfl⟩)

theorem B_gr_subquot (p a q' : ℕ) (haq : a + (q' + 1) = p) :
    ∃ s : SubQuot R (E₂I D a (q' + 1)),
      Nonempty ((↥(B D (q' + 2) p)
          ⧸ (B D (q' + 1) p).comap (B D (q' + 2) p).subtype)
        ≃ₗ[R] s.carrier) := by
  set f := ψ D p a q' haq
  set g := φ D p a q' haq
  have hker : LinearMap.ker f ≤ LinearMap.ker g := fun b hb =>
    LinearMap.mem_ker.mpr ((Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_comap.mpr
      (core_mem_B_pred D p a q' haq b (LinearMap.mem_ker.mp hb))))
  have hg : Function.Surjective g := (Submodule.mkQ_surjective _).comp fun ⟨z, hz⟩ => by
    obtain ⟨c, hcA, rfl⟩ := hz
    exact ⟨⟨c.1, (show p + 1 - (q' + 2) = a from by omega) ▸ (Submodule.mem_comap.mp hcA).1,
      c.2⟩, Subtype.ext rfl⟩
  let g' : ↥(LinearMap.range f) →ₗ[R] _ :=
    ((LinearMap.ker f).liftQ g hker).comp f.quotKerEquivRange.symm.toLinearMap
  have hg' : Function.Surjective g' := fun y => by
    obtain ⟨x, rfl⟩ := hg y
    exact ⟨f.quotKerEquivRange (Submodule.Quotient.mk x), by
      simp only [g', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
        Submodule.liftQ_apply]⟩
  exact ⟨⟨LinearMap.range f, (LinearMap.ker g').map (LinearMap.range f).subtype,
    Submodule.map_subtype_le _ _⟩,
    ⟨(LinearEquiv.ofTop _ (LinearMap.range_eq_top.mpr hg')).symm ≪≫ₗ
      g'.quotKerEquivRange.symm ≪≫ₗ
      (Submodule.quotEquivOfEq _ _
        (Submodule.comap_map_eq_of_injective
          (LinearMap.range f).injective_subtype (LinearMap.ker g'))).symm⟩⟩

end ZigZag

section Bfilt

variable {R : Type u} [CommRing R] (D : Bounded R)

def Bfilt : ∀ p', Fin (D.N + 1) → Submodule R (E₂I D p' 0)
  | 0, _ => ⊥
  | p + 1, i => B D (i.1 + 1) p

theorem Bfilt_gr (p' : ℕ) (i : Fin D.N) :
    ∃ a q, 1 ≤ q ∧ ∃ s : SubQuot R (E₂I D a q),
      Nonempty ((↥(Bfilt D p' i.succ)
          ⧸ (Bfilt D p' i.castSucc).comap (Bfilt D p' i.succ).subtype)
        ≃ₗ[R] s.carrier) := by
  match p' with
  | 0 =>

    haveI : Subsingleton ↥(Bfilt D 0 i.succ) :=
      show Subsingleton ↥(⊥ : Submodule R _) from inferInstance
    exact ⟨0, 1, le_refl 1, ⟨⊥, ⊥, le_refl ⊥⟩,
      ⟨leOfSubsingleton R _ _⟩⟩
  | p + 1 =>

    rcases le_or_gt (i.1 + 1) p with hip | hip
    ·
      exact ⟨p - i.1 - 1, i.1 + 1, Nat.succ_pos _,
        B_gr_subquot D p (p - i.1 - 1) i.1 (by omega)⟩
    ·
      have hle : B D (i.1 + 2) p ≤ B D (i.1 + 1) p := by
        refine Submodule.map_mono (Submodule.comap_mono ?_)
        show FilTot D (p + 1 - (i.1 + 2)) p ⊓ _
          ≤ FilTot D (p + 1 - (i.1 + 1)) p ⊓ _
        rw [show p + 1 - (i.1 + 2) = 0 from by omega,
          show p + 1 - (i.1 + 1) = 0 from by omega]
      haveI : Subsingleton (↥(Bfilt D (p + 1) i.succ)
          ⧸ (Bfilt D (p + 1) i.castSucc).comap
              (Bfilt D (p + 1) i.succ).subtype) := by
        refine Subsingleton.intro fun x y => ?_
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        rw [Submodule.Quotient.eq]
        exact Submodule.mem_comap.mpr (hle (Submodule.sub_mem _ x.2 y.2))
      exact ⟨0, 1, le_refl 1, ⟨⊥, ⊥, le_refl ⊥⟩,
        ⟨leOfSubsingleton R _ _⟩⟩

end Bfilt

section Hfilt

variable {R : Type u} [CommRing R] (D : Bounded R)

def Einf : ∀ p q, SubQuot R (E₂I D p q)
  | p, 0 => ⟨⊤, Bfilt D p (Fin.last D.N), le_top⟩
  | _, _ + 1 => ⟨⊤, ⊤, le_refl ⊤⟩

def τ (p : ℕ) : ↥(KerHV D p) →ₗ[R] ↥(FilH D p p) :=
  LinearMap.codRestrict _
    ((HTotB D p).mkQ ∘ₗ
      LinearMap.codRestrict (LinearMap.ker (dTot D p))
        ((LinearMap.single R (fun j : Diag p => D.C j.1.1 j.1.2)
            (edgeSlot p)).comp (KerHV D p).subtype)
        (fun x => edge_ker_rev D p x.1 x.2.1 x.2.2))
    (fun x => ⟨⟨_, edge_ker_rev D p x.1 x.2.1 x.2.2⟩,
      Submodule.mem_comap.mpr (edgeSingle_mem_FilTot D p x.1), rfl⟩)

theorem dTot_edgeSingle_of_ker_dV (p' : ℕ) (y : D.C p' 0)
    (hy : y ∈ LinearMap.ker (D.dV p' 0)) :
    dTot D p' (edgeSingle D p' y)
      = edgeSingle D (p' + 1) (D.dH p' 0 y) := by
  have hdF : dTot D p' (edgeSingle D p' y)
      ∈ FilTot D (p' + 1) (p' + 1) := by
    refine (mem_FilTot_succ_iff D (show p' + 1 = p' + 1 from rfl) _).mpr
      ⟨dTot_FilTot_le D p' p'
        ⟨_, edgeSingle_mem_FilTot D p' y, rfl⟩, ?_⟩
    rw [dTot_totSingle_col_same D (Nat.add_zero p') y,
      LinearMap.mem_ker.mp hy, smul_zero]
  refine funext fun i => ?_
  rcases eq_or_ne i (edgeSlot (p' + 1)) with rfl | hi
  · rw [show edgeSingle D (p' + 1) (D.dH p' 0 y) (edgeSlot (p' + 1))
        = D.dH p' 0 y from Pi.single_eq_same _ _]
    exact dTot_totSingle_col_succ D (Nat.add_zero p') y
  · exact ((mem_FilTot D _).mp hdF i (Diag_col_lt_of_ne i hi)).trans
      (Pi.single_eq_of_ne
        (M := fun j : Diag (p' + 1) => D.C j.1.1 j.1.2) hi _).symm

def σ (p : ℕ) :
    ↥(KerHV D p) →ₗ[R] (Einf D p 0).carrier :=
  (Submodule.mkQ _).comp (LinearMap.codRestrict _ (toE₂ D p) (fun _ => trivial))

def FilH_edge_iso (p : ℕ) :
    ↥(FilH D p p) ≃ₗ[R] (Einf D p 0).carrier := by
  have hτs : Function.Surjective (τ D p) := by
    rintro ⟨_, c, hcS, rfl⟩
    have hcF : c.1 ∈ FilTot D p p := Submodule.mem_comap.mp hcS
    refine ⟨⟨c.1 (edgeSlot p), edge_ker_fwd D p c.1 hcF c.2⟩,
      Subtype.ext (congrArg (HTotB D p).mkQ (Subtype.ext
        (show edgeSingle D p (c.1 (edgeSlot p)) = c.1 from
          congrArg Subtype.val ((edgeProj D p).left_inv ⟨c.1, hcF⟩))))⟩
  have hσs : Function.Surjective (σ D p) :=
    (Submodule.mkQ_surjective _).comp fun z =>
      (toE₂_surjective D p z.1).imp fun x hx => Subtype.ext hx
  have hστ : LinearMap.ker (σ D p) ≤ LinearMap.ker (τ D p) := by
    intro x hx
    have hxσ := (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.mem_ker.mp hx)
    have hxB : toE₂ D p x ∈ Bfilt D p (Fin.last D.N) :=
      Submodule.mem_comap.mp hxσ
    refine LinearMap.mem_ker.mpr (Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr ?_))
    clear hx hxσ
    match p, x, hxB with
    | 0, x, hxB =>
      have hx1 := (Submodule.Quotient.mk_eq_zero _).mp ((Submodule.mem_bot R).mp hxB)
      have hx2 : x.1 = 0 := congrArg Subtype.val ((Submodule.mem_bot R).mp
        ((Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val hx1)))
      refine (Submodule.mem_bot R).mpr (Subtype.ext ?_)
      show edgeSingle D 0 x.1 = 0
      rw [hx2]; exact Pi.single_zero _
    | p' + 1, x, hxB =>
      obtain ⟨⟨w, hwT⟩, _, hwη⟩ := hxB
      have hxw : toE₂ D (p' + 1)
          (x - ⟨zigOut D p' w, zigOut_mem_KerHV D p' w hwT⟩) = 0 := by
        rw [map_sub, sub_eq_zero]; exact hwη.symm
      obtain ⟨yc, hyc⟩ := (Submodule.Quotient.mk_eq_zero _).mp hxw
      obtain ⟨y, rfl⟩ := (colB D p' 0).mkQ_surjective yc
      have hdHy : D.dH p' 0 y.1 = x.1 - zigOut D p' w :=
        congrArg Subtype.val (congrArg (colH0_equiv D (p' + 1)) hyc)
      refine ⟨w + edgeSingle D p' y.1, ?_⟩
      show dTot D p' (w + edgeSingle D p' y.1)
        = edgeSingle D (p' + 1) x.1
      rw [map_add, dTot_eq_edgeSingle_zigOut D p' w hwT,
        dTot_edgeSingle_of_ker_dV D p' y.1 y.2, hdHy,
        ← Pi.single_add, add_sub_cancel]
  have hτσ : LinearMap.ker (τ D p) ≤ LinearMap.ker (σ D p) := by
    intro x hx
    have hxB : (⟨edgeSingle D p x.1, edge_ker_rev D p x.1 x.2.1 x.2.2⟩
        : ↥(LinearMap.ker (dTot D p))) ∈ HTotB D p :=
      (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val (LinearMap.mem_ker.mp hx))
    refine LinearMap.mem_ker.mpr
      ((Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_comap.mpr ?_))
    show toE₂ D p x ∈ Bfilt D p (Fin.last D.N)
    clear hx
    match p, x, hxB with
    | 0, x, hxB =>
      have h0 : edgeSingle D 0 x.1 = 0 :=
        congrArg Subtype.val ((Submodule.mem_bot R).mp hxB)
      have hx0 : x.1 = 0 := by
        have := congrFun h0 (edgeSlot 0)
        simpa only [edgeSingle, Pi.single_eq_same, Pi.zero_apply] using this
      exact (Submodule.mem_bot R).mpr (by rw [show x = 0 from Subtype.ext hx0, map_zero])
    | p' + 1, x, hxB =>
      rcases le_or_gt D.N (p' + 1) with hNp | hNp
      · haveI : Subsingleton (D.C (p' + 1) 0) := D.hBound (p' + 1) 0 (Or.inl hNp)
        rw [show x = 0 from Subsingleton.elim _ _, map_zero]; exact Submodule.zero_mem _
      · obtain ⟨w, hw⟩ := hxB
        have hw' : dTot D p' w = edgeSingle D (p' + 1) x.1 := hw
        have hwT : w ∈ zigTarget D p' :=
          Submodule.mem_comap.mpr (hw' ▸ edgeSingle_mem_FilTot D (p' + 1) x.1)
        have hwx : zigOut D p' w = x.1 := by
          have := congrFun hw' (edgeSlot (p' + 1))
          simp only [edgeSingle, Pi.single_eq_same] at this
          exact this
        refine ⟨⟨w, hwT⟩, Submodule.mem_comap.mpr ⟨?_, hwT⟩,
          congrArg (toE₂ D (p' + 1)) (Subtype.ext hwx)⟩
        show w ∈ FilTot D (p' + 1 - ((Fin.last D.N).1 + 1)) p'
        rw [Fin.val_last, show p' + 1 - (D.N + 1) = 0 from by omega,
          FilTot_zero]
        exact Submodule.mem_top
  exact ((LinearEquiv.ofTop _ (LinearMap.range_eq_top.mpr hτs)).symm ≪≫ₗ
      (τ D p).quotKerEquivRange.symm) ≪≫ₗ
    (Submodule.quotEquivOfEq _ _ (le_antisymm hτσ hστ)) ≪≫ₗ
    ((σ D p).quotKerEquivRange ≪≫ₗ
      LinearEquiv.ofTop _ (LinearMap.range_eq_top.mpr hσs))

def Hfilt (n : ℕ) (k : Fin (D.N + 2)) : Submodule R (HTot D n) :=
  if D.N ≤ n then (if (k : ℕ) = 0 then ⊥ else ⊤)
  else (if (k : ℕ) ≤ n then ⊥ else if (k : ℕ) = n + 1 then FilH D n n else ⊤)

theorem Hfilt_gr (p : Fin (D.N + 1)) :
    Nonempty (((Hfilt D (↑p) p.succ)
        ⧸ (Hfilt D (↑p) p.castSucc).comap (Hfilt D (↑p) p.succ).subtype)
      ≃ₗ[R] (Einf D (↑p) 0).carrier) := by
  have hps : ((p.succ : Fin (D.N + 2)) : ℕ) = (↑p : ℕ) + 1 := rfl
  have hpc : ((p.castSucc : Fin (D.N + 2)) : ℕ) = (↑p : ℕ) := rfl
  rcases Nat.lt_or_ge (↑p : ℕ) D.N with hpN | hpN
  ·
    have h1 : Hfilt D (↑p) p.succ = FilH D (↑p) (↑p) := by
      unfold Hfilt
      rw [hps, if_neg (Nat.not_le.mpr hpN), if_neg (by omega : ¬ (↑p : ℕ) + 1 ≤ ↑p), if_pos rfl]
    have h0 : Hfilt D (↑p) p.castSucc = ⊥ := by
      unfold Hfilt
      rw [hpc, if_neg (Nat.not_le.mpr hpN), if_pos (le_refl (↑p : ℕ))]
    refine ⟨?_ ≪≫ₗ FilH_edge_iso D (↑p)⟩
    exact (Submodule.quotEquivOfEqBot _ (by rw [h0, Submodule.comap_bot, Submodule.ker_subtype]))
      ≪≫ₗ LinearEquiv.ofEq _ _ h1
  ·

    haveI : Subsingleton (E₂I D (↑p) 0) :=
      have : Subsingleton (D.C (↑p) 0) := D.hBound (↑p) 0 (Or.inl hpN)
      inferInstance
    haveI : Subsingleton (↥(Hfilt D (↑p) p.succ)
        ⧸ (Hfilt D (↑p) p.castSucc).comap
            (Hfilt D (↑p) p.succ).subtype) := by
      rcases Nat.eq_zero_or_pos D.N with hN0 | hN0
      · haveI : Subsingleton (HTot D (↑p)) := by
          haveI : Subsingleton (Tot D (↑p)) :=
            ⟨fun f g => funext fun i =>
              @Subsingleton.elim _ (D.hBound i.1.1 i.1.2 (Or.inl (hN0.le.trans (Nat.zero_le _)))) _ _⟩
          infer_instance
        infer_instance
      · have hpN' : (↑p : ℕ) = D.N := le_antisymm (Nat.lt_succ_iff.mp p.2) hpN
        have h0 : Hfilt D (↑p) p.castSucc = ⊤ := by
          unfold Hfilt
          rw [hpc, if_pos hpN, if_neg (by omega : ¬ (↑p : ℕ) = 0)]
        rw [h0, Submodule.comap_top]; exact inferInstance
    exact ⟨leOfSubsingleton R _ _⟩

end Hfilt

theorem boundedSpectralSequence : BoundedSpectralSequence.{u} := by
  intro R _ D
  exact ⟨{
    Einf := Einf D
    hZ0 := fun _ => rfl
    Bfilt := Bfilt D
    Bfilt_mono := fun p' => match p' with
      | 0 => monotone_const
      | p + 1 => fun i j hij => B_mono D p (by omega : i.1 + 1 ≤ j.1 + 1)
    Bfilt_bot := fun p' => match p' with
      | 0 => rfl
      | p + 1 => B_one D p
    Bfilt_top := fun _ => rfl
    Bfilt_gr := Bfilt_gr D
    Hfilt := Hfilt D
    Hfilt_mono := fun n i j hij => by
      have hij' : (i : ℕ) ≤ (j : ℕ) := hij
      unfold Hfilt
      split_ifs <;> first | rfl | exact bot_le | exact le_top | omega
    Hfilt_bot := fun n => by
      have h0 : ((0 : Fin (D.N + 2)) : ℕ) = 0 := rfl
      show (if D.N ≤ n then _ else _) = ⊥
      rw [h0]; split_ifs with h1 h2 h3 <;> first | rfl | omega
    Hfilt_top := fun n => by
      have hl : ((Fin.last (D.N + 1) : Fin (D.N + 2)) : ℕ) = D.N + 1 := rfl
      show (if D.N ≤ n then _ else _) = ⊤
      rw [hl]
      by_cases h : D.N ≤ n
      · rw [if_pos h, if_neg (Nat.succ_ne_zero D.N)]
      · rw [if_neg h, if_neg (by omega : ¬ D.N + 1 ≤ n), if_neg (by omega : ¬ D.N + 1 = n + 1)]
    Hfilt_gr := Hfilt_gr D }⟩

end DoubleComplex

theorem solution : DoubleComplex.BoundedSpectralSequence.{u} := DoubleComplex.boundedSpectralSequence

end

end S_DoubleComplex_boundedSpectralSequence
end P2MW
export P2MW.S_DoubleComplex_boundedSpectralSequence (solution)
