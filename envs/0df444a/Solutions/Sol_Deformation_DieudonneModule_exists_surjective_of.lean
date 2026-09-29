-- Prove2me | solution 1 for Deformation.DieudonneModule.exists_surjective_of
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/055da14f-d87f-5b59-9070-c99b0d8f9a5d

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_exists_surjective_of

set_option autoImplicit false

open MvPolynomial

namespace Deformation
p2m_export "Deformation" "TruncWitt.map TruncWitt.map_truncate TruncWitt.map_map TruncWitt.shift TruncWitt.coeff_shift_zero TruncWitt.coeff_shift_succ comulRingHom wittHom mem_wittHom_iff map_counit_of_mem_wittHom natCast_eq_zero_of_algebra TruncWitt.shiftLE TruncWitt.coeff_shiftLE TruncWitt.shiftLE_succ shiftLE_mem_wittHom_iff wittHomShiftLE DieudonneModule DieudonneModule.of DieudonneModule.of_shiftLE DieudonneModule.exists_of"
namespace VerschiebungRelation
p2m_open "Deformation"

namespace Univ

variable (p : ℕ) [hp : Fact p.Prime]

abbrev Var : Type := ZMod p × ℕ

abbrev U : Type := MvPolynomial (ZMod p × ℕ) (ZMod p)

def τ (r : ZMod p) : Var p ≃ Var p := Equiv.prodCongr (Equiv.addRight r) (Equiv.refl ℕ)

@[scoped simp] theorem τ_apply (r : ZMod p) (v : Var p) : τ p r v = (v.1 + r, v.2) := rfl

theorem τ_symm_apply (r : ZMod p) (v : Var p) : (τ p r).symm v = (v.1 - r, v.2) := by
  rcases v with ⟨j, l⟩
  simp [τ, Equiv.prodCongr, sub_eq_add_neg]

noncomputable def ρ (r : ZMod p) : U p →ₐ[ZMod p] U p := rename (τ p r)

@[scoped simp] theorem ρ_X (r : ZMod p) (v : Var p) : ρ p r (X v) = X (v.1 + r, v.2) := by
  simp [ρ, rename_X]

theorem ρ_zero (f : U p) : ρ p 0 f = f := by
  have : (⇑(τ p 0) : Var p → Var p) = id := funext fun v => by simp
  simp [ρ, this, rename_id]

theorem ρ_ρ (r s : ZMod p) (f : U p) : ρ p r (ρ p s f) = ρ p (s + r) f := by
  simp only [ρ, rename_rename]
  have : (⇑(τ p r) ∘ ⇑(τ p s) : Var p → Var p) = ⇑(τ p (s + r)) := funext fun v => by
    simp [add_assoc]
  rw [this]

noncomputable def sh (r : ZMod p) (d : Var p →₀ ℕ) : Var p →₀ ℕ := d.mapDomain (τ p r)

theorem sh_apply (r : ZMod p) (d : Var p →₀ ℕ) (j : ZMod p) (l : ℕ) :
    sh p r d (j, l) = d (j - r, l) := by
  rw [sh, Finsupp.mapDomain_equiv_apply, τ_symm_apply]

@[scoped simp] theorem sh_zero (d : Var p →₀ ℕ) : sh p 0 d = d := by
  ext ⟨j, l⟩; simp [sh_apply]

theorem sh_sh (r s : ZMod p) (d : Var p →₀ ℕ) : sh p r (sh p s d) = sh p (r + s) d := by
  ext ⟨j, l⟩
  simp only [sh_apply]
  congr 2
  abel

theorem ρ_monomial (r : ZMod p) (d : Var p →₀ ℕ) (c : ZMod p) :
    ρ p r (monomial d c) = monomial (sh p r d) c := by
  simp [ρ, sh, rename_monomial]

theorem coeff_ρ (r : ZMod p) (d : Var p →₀ ℕ) (f : U p) :
    coeff d (ρ p r f) = coeff (sh p (-r) d) f := by
  have h : sh p r (sh p (-r) d) = d := by rw [sh_sh, add_neg_cancel, sh_zero]
  conv_lhs => rw [← h]
  exact coeff_rename_mapDomain _ (τ p r).injective _ _

def IsFixed (d : Var p →₀ ℕ) : Prop := ∀ (j : ZMod p) (l : ℕ), d (j, l) = d (0, l)

theorem sh_eq_self_of_isFixed {d : Var p →₀ ℕ} (hd : IsFixed p d) (r : ZMod p) : sh p r d = d := by
  ext ⟨j, l⟩
  rw [sh_apply, hd (j - r) l, hd j l]

theorem isFixed_of_sh_one {d : Var p →₀ ℕ} (hd : sh p 1 d = d) : IsFixed p d := by
  have step : ∀ (j : ZMod p) (l : ℕ), d (j, l) = d (j - 1, l) := fun j l => by
    conv_lhs => rw [← hd]
    rw [sh_apply]
  have key : ∀ (n : ℕ) (l : ℕ), d ((n : ZMod p), l) = d (0, l) := by
    intro n l
    induction n with
    | zero => simp
    | succ n ih => rw [step, Nat.cast_succ, add_sub_cancel_right, ih]
  intro j l
  rw [← ZMod.natCast_zmod_val j, key]

theorem isFixed_sh_iff (r : ZMod p) (d : Var p →₀ ℕ) : IsFixed p (sh p r d) ↔ IsFixed p d := by
  constructor
  · intro h j l
    have h1 := h (j + r) l
    have h2 := h (0 + r) l
    rw [sh_apply, add_sub_cancel_right] at h1
    rw [zero_add, sh_apply, sub_self] at h2
    rw [h1, ← h2]
  · intro h j l
    rw [sh_apply, sh_apply, h (j - r), h (0 - r)]

theorem eq_zero_of_sh_eq_self {d : Var p →₀ ℕ} (hd : ¬ IsFixed p d) {r : ZMod p}
    (hr : sh p r d = d) : r = 0 := by
  by_contra hr0
  have key : ∀ n : ℕ, sh p ((n : ZMod p) * r) d = d := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, add_comm, ← sh_sh, ih, hr]
  apply hd
  apply isFixed_of_sh_one
  have h := key (r⁻¹ : ZMod p).val
  rwa [ZMod.natCast_zmod_val, inv_mul_cancel₀ hr0] at h

def orbitSet (d : Var p →₀ ℕ) : Set (Var p →₀ ℕ) := {d' | ∃ r : ZMod p, sh p r d = d'}

theorem orbitSet_sh (r : ZMod p) (d : Var p →₀ ℕ) : orbitSet p (sh p r d) = orbitSet p d := by
  ext d'
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s + r, by rw [sh_sh]⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s - r, by rw [sh_sh, sub_add_cancel]⟩

noncomputable def rep (d : Var p →₀ ℕ) : Var p →₀ ℕ :=
  Classical.epsilon fun d' => d' ∈ orbitSet p d

theorem rep_mem (d : Var p →₀ ℕ) : rep p d ∈ orbitSet p d :=
  Classical.epsilon_spec (p := fun d' => d' ∈ orbitSet p d) ⟨d, ⟨0, sh_zero p d⟩⟩

theorem rep_sh (r : ZMod p) (d : Var p →₀ ℕ) : rep p (sh p r d) = rep p d := by
  unfold rep
  rw [orbitSet_sh]

noncomputable def tr (g : U p) : U p := ∑ r : ZMod p, ρ p r g

theorem coeff_tr (g : U p) (d : Var p →₀ ℕ) :
    coeff d (tr p g) = ∑ r : ZMod p, coeff (sh p (-r) d) g := by
  simp only [tr, coeff_sum, coeff_ρ]

theorem exists_eq_tr_add {f : U p} (hf : ∀ r : ZMod p, ρ p r f = f) :
    ∃ g h : U p, f = tr p g + h ∧ (∀ d, IsFixed p d → coeff d h = coeff d f) ∧
      (∀ d, ¬ IsFixed p d → coeff d h = 0) := by
  classical
  have hinv : ∀ (r : ZMod p) (d : Var p →₀ ℕ), coeff (sh p r d) f = coeff d f := by
    intro r d
    have := coeff_ρ p r (sh p r d) f
    rwa [hf, sh_sh, neg_add_cancel, sh_zero] at this

  let g : U p := ∑ d ∈ f.support with (¬ IsFixed p d ∧ rep p d = d), monomial d (coeff d f)
  have hg : ∀ d, coeff d g = if (¬ IsFixed p d ∧ rep p d = d) then coeff d f else 0 := by
    intro d
    simp only [g, coeff_sum, coeff_monomial]
    rw [Finset.sum_ite_eq' (f.support.filter _) d (fun x => coeff x f)]
    simp only [Finset.mem_filter, mem_support_iff, ne_eq]
    by_cases h : ¬IsFixed p d ∧ rep p d = d
    · by_cases h0 : coeff d f = 0
      · simp [h, h0]
      · simp [h, h0]
    · simp [h]
  have htr : ∀ d, coeff d (tr p g) = if IsFixed p d then 0 else coeff d f := by
    intro d
    rw [coeff_tr]
    simp only [hg]
    by_cases hd : IsFixed p d
    · rw [if_pos hd]
      refine Finset.sum_eq_zero fun r _ => ?_
      rw [if_neg]
      rintro ⟨h1, -⟩
      exact h1 ((isFixed_sh_iff p _ d).2 hd)
    · rw [if_neg hd]

      obtain ⟨r₀, hr₀⟩ : ∃ r₀ : ZMod p, sh p (-r₀) d = rep p d := by
        obtain ⟨s, hs⟩ := rep_mem p d
        exact ⟨-s, by rw [neg_neg, hs]⟩
      rw [Finset.sum_eq_single r₀]
      · rw [if_pos, hinv]
        refine ⟨fun h => hd ((isFixed_sh_iff p _ d).1 h), ?_⟩
        rw [rep_sh, hr₀]
      · intro r _ hr
        rw [if_neg]
        rintro ⟨-, h2⟩
        rw [rep_sh] at h2
        apply hr

        have h3 : sh p (r₀ - r) d = d := by
          have := congrArg (sh p r₀) (h2.symm.trans hr₀.symm)
          rwa [sh_sh, sh_sh, add_neg_cancel, sh_zero, ← sub_eq_add_neg] at this
        have := eq_zero_of_sh_eq_self p hd h3
        rwa [sub_eq_zero, eq_comm] at this
      · intro h; exact absurd (Finset.mem_univ r₀) h
  refine ⟨g, f - tr p g, by abel, fun d hd => ?_, fun d hd => ?_⟩
  · rw [coeff_sub, htr, if_pos hd, sub_zero]
  · rw [coeff_sub, htr, if_neg hd, sub_self]

noncomputable def diag : U p →ₐ[ZMod p] MvPolynomial ℕ (ZMod p) := rename Prod.snd

theorem diag_ρ (r : ZMod p) (f : U p) : diag p (ρ p r f) = diag p f := by
  simp only [diag, ρ, rename_rename]
  rfl

theorem diag_tr (g : U p) : diag p (tr p g) = 0 := by
  simp only [tr, map_sum, diag_ρ, Finset.sum_const, Finset.card_univ, ZMod.card]
  rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]

theorem mapDomain_snd_apply (d : Var p →₀ ℕ) (l : ℕ) :
    d.mapDomain Prod.snd l = ∑ j : ZMod p, d (j, l) := by
  classical
  induction d using Finsupp.induction with
  | zero => simp
  | single_add a m f _ _ ih =>
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.add_apply, ih]
    simp only [Finsupp.add_apply, Finset.sum_add_distrib]
    congr 1
    rcases a with ⟨j₀, l₀⟩
    simp only [Finsupp.single_apply, Prod.mk.injEq]
    by_cases h : l₀ = l
    · subst h
      simp
    · simp [h]

theorem mapDomain_snd_apply_of_isFixed {d : Var p →₀ ℕ} (hd : IsFixed p d) (l : ℕ) :
    d.mapDomain Prod.snd l = p * d (0, l) := by
  rw [mapDomain_snd_apply]
  simp only [hd _ l, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]

theorem eq_of_isFixed_of_mapDomain_eq {d d' : Var p →₀ ℕ} (hd : IsFixed p d) (hd' : IsFixed p d')
    (h : d.mapDomain Prod.snd = d'.mapDomain Prod.snd) : d = d' := by
  ext ⟨j, l⟩
  have := congrArg (fun e => e l) h
  simp only [mapDomain_snd_apply_of_isFixed p hd, mapDomain_snd_apply_of_isFixed p hd'] at this
  rw [hd, hd']
  exact Nat.eq_of_mul_eq_mul_left hp.out.pos this

theorem coeff_diag_of_isFixed {h : U p} (hh : ∀ d, ¬ IsFixed p d → coeff d h = 0)
    {d : Var p →₀ ℕ} (hd : IsFixed p d) :
    coeff (d.mapDomain Prod.snd) (diag p h) = coeff d h := by
  classical
  conv_lhs => rw [as_sum h]
  simp only [diag, map_sum, rename_monomial, coeff_sum, coeff_monomial]
  rw [Finset.sum_congr rfl (g := fun x => if x = d then coeff x h else 0)]
  · rw [Finset.sum_ite_eq']
    split_ifs with hmem
    · rfl
    · exact (notMem_support_iff.1 hmem).symm
  · intro x hx
    have hxf : IsFixed p x := by
      by_contra hxf
      exact (mem_support_iff.1 hx) (hh x hxf)
    by_cases hxd : x = d
    · subst hxd; simp
    · rw [if_neg hxd, if_neg]
      intro heq
      exact hxd (eq_of_isFixed_of_mapDomain_eq p hxf hd heq)

noncomputable def Yvec (j : ZMod p) : WittVector p (U p) := WittVector.mk p fun l => X (j, l)

noncomputable def S : WittVector p (U p) := ∑ j : ZMod p, Yvec p j

theorem map_ρ_Yvec (r j : ZMod p) :
    WittVector.map (ρ p r).toRingHom (Yvec p j) = Yvec p (j + r) := by
  ext l
  simp [Yvec, WittVector.map_coeff]

theorem ρ_S_coeff (r : ZMod p) (i : ℕ) : ρ p r ((S p).coeff i) = (S p).coeff i := by
  have : WittVector.map (ρ p r).toRingHom (S p) = S p := by
    simp only [S, map_sum, map_ρ_Yvec]
    exact Fintype.sum_equiv (Equiv.addRight r) _ _ fun j => rfl
  have h := congrArg (fun x => x.coeff i) this
  simp only [WittVector.map_coeff] at h
  exact h

noncomputable def Ydiag : WittVector p (MvPolynomial ℕ (ZMod p)) := WittVector.mk p fun l => X l

theorem map_diag_Yvec (j : ZMod p) : WittVector.map (diag p).toRingHom (Yvec p j) = Ydiag p := by
  ext l
  simp [Yvec, Ydiag, WittVector.map_coeff, diag, rename_X]

theorem map_diag_S : WittVector.map (diag p).toRingHom (S p) = Ydiag p * p := by
  simp only [S, map_sum, map_diag_Yvec, Finset.sum_const, Finset.card_univ, ZMod.card]
  rw [nsmul_eq_mul']

theorem diag_S_coeff_zero : diag p ((S p).coeff 0) = 0 := by
  have h := congrArg (fun x => x.coeff 0) (map_diag_S p)
  simp only [WittVector.map_coeff, WittVector.mul_charP_coeff_zero] at h
  exact h

theorem diag_S_coeff_succ (i : ℕ) : diag p ((S p).coeff (i + 1)) = X i ^ p := by
  have h := congrArg (fun x => x.coeff (i + 1)) (map_diag_S p)
  simp only [WittVector.map_coeff, WittVector.mul_charP_coeff_succ] at h
  simpa [Ydiag] using h

noncomputable def e (i : ℕ) : Var p →₀ ℕ := ∑ j : ZMod p, Finsupp.single (j, i) 1

theorem e_apply (i : ℕ) (j : ZMod p) (l : ℕ) : e p i (j, l) = if l = i then 1 else 0 := by
  classical
  simp only [e, Finsupp.finsetSum_apply, Finsupp.single_apply, Prod.mk.injEq]
  by_cases h : l = i
  · subst h
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun x _ => by simp [Ne.symm h]

theorem isFixed_e (i : ℕ) : IsFixed p (e p i) := fun j l => by rw [e_apply, e_apply]

theorem mapDomain_snd_e (i : ℕ) : (e p i).mapDomain Prod.snd = Finsupp.single i p := by
  ext l
  rw [mapDomain_snd_apply_of_isFixed p (isFixed_e p i), e_apply, Finsupp.single_apply]
  by_cases h : l = i
  · subst h; simp
  · simp [h, Ne.symm h]

noncomputable def nm (i : ℕ) : U p := ∏ j : ZMod p, X (j, i)

theorem nm_eq_monomial (i : ℕ) : nm p i = monomial (e p i) 1 := by
  rw [e, monomial_sum_index, C_1, one_mul]
  rfl

theorem S_coeff_zero : ∃ g : U p, (S p).coeff 0 = tr p g := by
  classical
  obtain ⟨g, h, hf, hfix, hnfix⟩ := exists_eq_tr_add p (ρ_S_coeff p · 0)
  refine ⟨g, ?_⟩
  suffices hh : h = 0 by rw [hf, hh, add_zero]
  ext d
  rw [coeff_zero]
  by_cases hd : IsFixed p d
  · rw [← coeff_diag_of_isFixed p hnfix hd]
    have : diag p h = 0 := by
      have := congrArg (diag p) hf
      rwa [diag_S_coeff_zero, map_add, diag_tr, zero_add, eq_comm] at this
    rw [this, coeff_zero]
  · exact hnfix d hd

theorem S_coeff_succ (i : ℕ) : ∃ g : U p, (S p).coeff (i + 1) = tr p g + nm p i := by
  classical
  obtain ⟨g, h, hf, hfix, hnfix⟩ := exists_eq_tr_add p (ρ_S_coeff p · (i + 1))
  refine ⟨g, ?_⟩
  suffices hh : h = nm p i by rw [hf, hh]
  have hdiag : diag p h = X i ^ p := by
    have := congrArg (diag p) hf
    rwa [diag_S_coeff_succ, map_add, diag_tr, zero_add, eq_comm] at this
  rw [nm_eq_monomial]
  ext d
  rw [coeff_monomial]
  by_cases hd : IsFixed p d
  · rw [← coeff_diag_of_isFixed p hnfix hd, hdiag]
    have hX : (X i : MvPolynomial ℕ (ZMod p)) ^ p = monomial (Finsupp.single i p) 1 := by
      rw [X_pow_eq_monomial]
    rw [hX, coeff_monomial]
    by_cases hde : e p i = d
    · subst hde
      rw [if_pos (mapDomain_snd_e p i).symm, if_pos rfl]
    · rw [if_neg hde, if_neg]
      intro heq
      apply hde
      exact eq_of_isFixed_of_mapDomain_eq p (isFixed_e p i) hd ((mapDomain_snd_e p i).trans heq)
  · rw [hnfix d hd, if_neg]
    rintro rfl
    exact hd (isFixed_e p i)

end Univ
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation.VerschiebungRelation.Univ"

end Deformation.VerschiebungRelation
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation.VerschiebungRelation.Univ P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation.VerschiebungRelation"
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation.VerschiebungRelation.Univ P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation"

namespace Deformation
p2m_export "Deformation" "TruncWitt.map TruncWitt.map_truncate TruncWitt.map_map TruncWitt.shift TruncWitt.coeff_shift_zero TruncWitt.coeff_shift_succ comulRingHom wittHom mem_wittHom_iff map_counit_of_mem_wittHom natCast_eq_zero_of_algebra TruncWitt.shiftLE TruncWitt.coeff_shiftLE TruncWitt.shiftLE_succ shiftLE_mem_wittHom_iff wittHomShiftLE DieudonneModule DieudonneModule.of DieudonneModule.of_shiftLE DieudonneModule.exists_of"
namespace VerschiebungRelation
p2m_open "Deformation"

open TensorProduct

universe u v w

section PointDatum

variable (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime]
variable (A : Type v) [CommRing A] [Bialgebra k A]
variable (T : Type w) [CommRing T] [Algebra k T]
variable (β : WithConv (A →ₗ[k] T))

structure PointDatum (n : ℕ) where

  C : Type v
  [instCommRing : CommRing C]
  [instAlgebra : Algebra k C]

  ι : Fin n → (A →ₐ[k] C)

  lam : C →ₗ[k] T

  δ : A →ₐ[k] C
  lam_prod : ∀ a : Fin n → A, lam (∏ j, ι j (a j)) = ∏ j, β.ofConv (a j)
  lam_comp : lam ∘ₗ δ.toLinearMap = (β ^ n).ofConv
  map_δ : ∀ (m : ℕ) (x : TruncatedWittVector p m A), x ∈ wittHom k p m A →
    TruncWitt.map δ.toRingHom x = ∑ j, TruncWitt.map (ι j).toRingHom x

attribute [scoped instance] PointDatum.instCommRing PointDatum.instAlgebra

namespace PointDatum

variable {k p A T β}

noncomputable def zero : PointDatum k p A T β 0 where
  C := A
  ι := fun j => j.elim0
  lam := Algebra.linearMap k T ∘ₗ Coalgebra.counit
  δ := (Algebra.ofId k A).comp (Bialgebra.counitAlgHom k A)
  lam_prod a := by
    simp [Bialgebra.counit_one]
  lam_comp := by
    rw [pow_zero, LinearMap.convOne_def]
    refine LinearMap.ext fun a => ?_
    simp [Bialgebra.counit_algebraMap]
  map_δ m x hx := by
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    have h : ((Algebra.ofId k A).comp (Bialgebra.counitAlgHom k A)).toRingHom =
        (algebraMap k A).comp (Bialgebra.counitAlgHom k A).toRingHom := rfl
    rw [h, ← TruncWitt.map_map, map_counit_of_mem_wittHom hx, map_zero]

variable {n : ℕ}

noncomputable def succ (D : PointDatum k p A T β n) : PointDatum k p A T β (n + 1) where
  C := A ⊗[k] D.C
  ι := Fin.cons (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] D.C)
    fun j => (Algebra.TensorProduct.includeRight : D.C →ₐ[k] A ⊗[k] D.C).comp (D.ι j)
  lam := LinearMap.mul' k T ∘ₗ TensorProduct.map β.ofConv D.lam
  δ := (Algebra.TensorProduct.map (AlgHom.id k A) D.δ).comp (Bialgebra.comulAlgHom k A)
  lam_prod a := by
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.cons_zero]
    simp only [Fin.cons_succ, AlgHom.coe_comp, Function.comp_apply]
    rw [← map_prod (Algebra.TensorProduct.includeRight : D.C →ₐ[k] A ⊗[k] D.C),
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, LinearMap.comp_apply,
      TensorProduct.map_tmul, LinearMap.mul'_apply, D.lam_prod]
  lam_comp := by
    rw [pow_succ', LinearMap.convMul_def, WithConv.ofConv_toConv, ← D.lam_comp]
    have key : TensorProduct.map β.ofConv D.lam ∘ₗ
        (Algebra.TensorProduct.map (AlgHom.id k A) D.δ).toLinearMap =
        TensorProduct.map β.ofConv (D.lam ∘ₗ D.δ.toLinearMap) :=
      TensorProduct.ext' fun a c => by simp
    refine LinearMap.ext fun a => ?_
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.coe_comp,
      Function.comp_apply, Bialgebra.comulAlgHom_apply]
    rw [← key]
    rfl
  map_δ m x hx := by
    have h0 : ((Algebra.TensorProduct.map (AlgHom.id k A) D.δ).comp
        (Bialgebra.comulAlgHom k A)).toRingHom =
        (Algebra.TensorProduct.map (AlgHom.id k A) D.δ).toRingHom.comp (comulRingHom k A) := rfl
    have h1 : (Algebra.TensorProduct.map (AlgHom.id k A) D.δ).toRingHom.comp
        (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] A).toRingHom =
        (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] D.C).toRingHom := by
      have := Algebra.TensorProduct.map_comp_includeLeft (AlgHom.id k A) D.δ
      rw [AlgHom.comp_id] at this
      exact congrArg AlgHom.toRingHom this
    have h2 : (Algebra.TensorProduct.map (AlgHom.id k A) D.δ).toRingHom.comp
        (Algebra.TensorProduct.includeRight : A →ₐ[k] A ⊗[k] A).toRingHom =
        (Algebra.TensorProduct.includeRight : D.C →ₐ[k] A ⊗[k] D.C).toRingHom.comp
          D.δ.toRingHom := by
      exact congrArg AlgHom.toRingHom (Algebra.TensorProduct.map_comp_includeRight (AlgHom.id k A) D.δ)
    rw [h0, ← TruncWitt.map_map, (mem_wittHom_iff x).1 hx, map_add, TruncWitt.map_map,
      TruncWitt.map_map, h1, h2, ← TruncWitt.map_map, D.map_δ m x hx, map_sum, Fin.sum_univ_succ,
      Fin.cons_zero]
    simp only [Fin.cons_succ, TruncWitt.map_map]
    rfl

end PointDatum
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation.VerschiebungRelation.Univ P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation.VerschiebungRelation"

noncomputable def pointDatum : (n : ℕ) → PointDatum k p A T β n
  | 0 => PointDatum.zero
  | n + 1 => (pointDatum n).succ

end PointDatum
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation.VerschiebungRelation.Univ P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation.VerschiebungRelation"

end Deformation.VerschiebungRelation
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation.VerschiebungRelation.Univ P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation.VerschiebungRelation"
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation.VerschiebungRelation.Univ P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation.VerschiebungRelation"

namespace Deformation
p2m_export "Deformation" "TruncWitt.map TruncWitt.map_truncate TruncWitt.map_map TruncWitt.shift TruncWitt.coeff_shift_zero TruncWitt.coeff_shift_succ comulRingHom wittHom mem_wittHom_iff map_counit_of_mem_wittHom natCast_eq_zero_of_algebra TruncWitt.shiftLE TruncWitt.coeff_shiftLE TruncWitt.shiftLE_succ shiftLE_mem_wittHom_iff wittHomShiftLE DieudonneModule DieudonneModule.of DieudonneModule.of_shiftLE DieudonneModule.exists_of"
namespace VerschiebungRelation
p2m_open "Deformation"

open MvPolynomial TensorProduct

universe u v w

section Main

variable (k : Type u) [CommRing k] (p : ℕ) [hp : Fact p.Prime]
variable (A : Type v) [CommRing A] [Bialgebra k A]
variable (T : Type w) [CommRing T] [Algebra k T]
variable (β : WithConv (A →ₗ[k] T))

noncomputable def Dp : PointDatum k p A T β p := pointDatum k p A T β p

noncomputable def eZ : ZMod p ≃ Fin p := (ZMod.finEquiv p).toEquiv.symm

noncomputable def ιZ (j : ZMod p) : A →ₐ[k] (Dp k p A T β).C := (Dp k p A T β).ι (eZ p j)

theorem lam_prod_Z (a : ZMod p → A) :
    (Dp k p A T β).lam (∏ j : ZMod p, ιZ k p A T β j (a j)) = ∏ j : ZMod p, β.ofConv (a j) := by
  have h1 : ∏ j : ZMod p, ιZ k p A T β j (a j) =
      ∏ j : Fin p, (Dp k p A T β).ι j (a ((eZ p).symm j)) :=
    Fintype.prod_equiv (eZ p) _ _ fun j => by simp [ιZ]
  have h2 : ∏ j : ZMod p, β.ofConv (a j) = ∏ j : Fin p, β.ofConv (a ((eZ p).symm j)) :=
    Fintype.prod_equiv (eZ p) _ _ fun j => by simp
  rw [h1, h2, (Dp k p A T β).lam_prod]

theorem map_δ_Z {m : ℕ} {x : TruncatedWittVector p m A} (hx : x ∈ wittHom k p m A) :
    TruncWitt.map (Dp k p A T β).δ.toRingHom x =
      ∑ j : ZMod p, TruncWitt.map (ιZ k p A T β j).toRingHom x := by
  rw [(Dp k p A T β).map_δ m x hx]
  exact (Fintype.sum_equiv (eZ p) _ _ fun j => rfl).symm

theorem finsupp_prod_eq (d : Univ.Var p →₀ ℕ) (g : Univ.Var p → (Dp k p A T β).C) :
    d.prod (fun v n => g v ^ n) =
      ∏ j : ZMod p, ∏ l ∈ d.support.image Prod.snd, g (j, l) ^ d (j, l) := by
  classical
  rw [Finsupp.prod, ← Finset.prod_product (s := Finset.univ) (t := d.support.image Prod.snd)
    (f := fun v => g v ^ d v)]
  refine Finset.prod_subset ?_ ?_
  · intro v hv
    exact Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_image.2 ⟨v, hv, rfl⟩⟩
  · intro v _ hv
    rw [Finsupp.notMem_support_iff.1 hv, pow_zero]

theorem lam_δ (a : A) : (Dp k p A T β).lam ((Dp k p A T β).δ a) = (β ^ p).ofConv a := by
  have := LinearMap.congr_fun (Dp k p A T β).lam_comp a
  simpa using this

variable [CharP k p] (y : WittVector p A)

noncomputable def ev : Univ.U p →+* (Dp k p A T β).C :=
  MvPolynomial.eval₂Hom ((algebraMap k (Dp k p A T β).C).comp (ZMod.castHom (dvd_refl p) k))
    fun v => ιZ k p A T β v.1 (y.coeff v.2)

noncomputable def av (d : Univ.Var p →₀ ℕ) (j : ZMod p) : A :=
  ∏ l ∈ d.support.image Prod.snd, y.coeff l ^ d (j, l)

theorem lam_ev_ρ_monomial (r : ZMod p) (d : Univ.Var p →₀ ℕ) (c : ZMod p) :
    (Dp k p A T β).lam (ev k p A T β y (Univ.ρ p r (monomial d c))) =
      (ZMod.castHom (dvd_refl p) k c) • ∏ j : ZMod p, β.ofConv (av p A y d j) := by
  classical
  rw [Univ.ρ_monomial, ev, eval₂Hom_monomial, Univ.sh,
    Finsupp.prod_mapDomain_index_inj (Univ.τ p r).injective]
  have h1 : (d.prod fun v n => (ιZ k p A T β ((Univ.τ p r) v).1 (y.coeff ((Univ.τ p r) v).2)) ^ n) =
      ∏ j : ZMod p, ιZ k p A T β (j + r) (av p A y d j) := by
    rw [finsupp_prod_eq k p A T β d
      (fun v => ιZ k p A T β ((Univ.τ p r) v).1 (y.coeff ((Univ.τ p r) v).2))]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Univ.τ_apply, av, map_prod, map_pow]
  have h2 : ∏ j : ZMod p, ιZ k p A T β (j + r) (av p A y d j) =
      ∏ j : ZMod p, ιZ k p A T β j (av p A y d (j - r)) :=
    Fintype.prod_equiv (Equiv.addRight r) _ _ fun j => by simp
  have h3 : ∏ j : ZMod p, β.ofConv (av p A y d (j - r)) = ∏ j : ZMod p, β.ofConv (av p A y d j) :=
    Fintype.prod_equiv (Equiv.subRight r) _ _ fun j => by simp
  rw [h1, h2, RingHom.comp_apply, ← Algebra.smul_def, map_smul, lam_prod_Z, h3]

theorem lam_ev_ρ (r : ZMod p) (g : Univ.U p) :
    (Dp k p A T β).lam (ev k p A T β y (Univ.ρ p r g)) = (Dp k p A T β).lam (ev k p A T β y g) := by
  have H : ∀ s : ZMod p, (Dp k p A T β).lam (ev k p A T β y (Univ.ρ p s g)) =
      ∑ d ∈ g.support, (ZMod.castHom (dvd_refl p) k (coeff d g)) •
        ∏ j : ZMod p, β.ofConv (av p A y d j) := by
    intro s
    conv_lhs => rw [as_sum g]
    simp only [map_sum, lam_ev_ρ_monomial]
  rw [H r, ← H 0, Univ.ρ_zero]

theorem map_ev_Yvec (j : ZMod p) :
    WittVector.map (ev k p A T β y) (Univ.Yvec p j) =
      WittVector.map (ιZ k p A T β j).toRingHom y := by
  ext l
  simp [Univ.Yvec, WittVector.map_coeff, ev]

theorem map_ev_S :
    WittVector.map (ev k p A T β y) (Univ.S p) =
      ∑ j : ZMod p, WittVector.map (ιZ k p A T β j).toRingHom y := by
  simp only [Univ.S, map_sum, map_ev_Yvec]

theorem δ_coeff_eq_ev_S_coeff {n : ℕ} (hy : WittVector.truncate n y ∈ wittHom k p n A)
    (i : ℕ) (hi : i < n) :
    (Dp k p A T β).δ (y.coeff i) = ev k p A T β y ((Univ.S p).coeff i) := by
  have h := map_δ_Z k p A T β hy
  simp only [TruncWitt.map_truncate] at h
  rw [← map_sum, ← map_ev_S] at h
  have h' := congrArg (TruncatedWittVector.coeff ⟨i, hi⟩) h
  rw [WittVector.coeff_truncate, WittVector.coeff_truncate, WittVector.map_coeff,
    WittVector.map_coeff] at h'
  exact h'

theorem lam_ev_nm (i : ℕ) :
    (Dp k p A T β).lam (ev k p A T β y (Univ.nm p i)) = (β.ofConv (y.coeff i)) ^ p := by
  simp only [Univ.nm, map_prod, ev, eval₂Hom_X']
  rw [lam_prod_Z, Finset.prod_const, Finset.card_univ, ZMod.card]

theorem lam_ev_tr (g : Univ.U p) :
    (Dp k p A T β).lam (ev k p A T β y (Univ.tr p g)) = 0 := by
  simp only [Univ.tr, map_sum, lam_ev_ρ, Finset.sum_const, Finset.card_univ, ZMod.card]
  rw [nsmul_eq_mul, natCast_eq_zero_of_algebra k p T, zero_mul]

theorem main {n : ℕ} {x : TruncatedWittVector p n A} (hx : x ∈ wittHom k p n A) :
    (∀ (h : 0 < n), (β ^ p).ofConv (x.coeff ⟨0, h⟩) = 0) ∧
    ∀ (i : ℕ) (hi : i + 1 < n),
      (β ^ p).ofConv (x.coeff ⟨i + 1, hi⟩) = (β.ofConv (x.coeff ⟨i, Nat.lt_of_succ_lt hi⟩)) ^ p := by
  obtain ⟨y, rfl⟩ := WittVector.truncate_surjective p n A x
  refine ⟨fun h => ?_, fun i hi => ?_⟩
  · obtain ⟨g, hg⟩ := Univ.S_coeff_zero p
    rw [WittVector.coeff_truncate, Fin.val_mk, ← lam_δ, δ_coeff_eq_ev_S_coeff k p A T β y hx 0 h,
      hg, lam_ev_tr]
  · obtain ⟨g, hg⟩ := Univ.S_coeff_succ p i
    rw [WittVector.coeff_truncate, WittVector.coeff_truncate, Fin.val_mk, Fin.val_mk, ← lam_δ,
      δ_coeff_eq_ev_S_coeff k p A T β y hx (i + 1) hi, hg, map_add, map_add, lam_ev_tr, zero_add,
      lam_ev_nm]

end Main
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation.VerschiebungRelation.Univ P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation.VerschiebungRelation"

end Deformation.VerschiebungRelation
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation.VerschiebungRelation.Univ P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation.VerschiebungRelation"
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation.VerschiebungRelation.Univ P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation.VerschiebungRelation"

namespace Deformation
p2m_export "Deformation" "TruncWitt.map TruncWitt.map_truncate TruncWitt.map_map TruncWitt.shift TruncWitt.coeff_shift_zero TruncWitt.coeff_shift_succ comulRingHom wittHom mem_wittHom_iff map_counit_of_mem_wittHom natCast_eq_zero_of_algebra TruncWitt.shiftLE TruncWitt.coeff_shiftLE TruncWitt.shiftLE_succ shiftLE_mem_wittHom_iff wittHomShiftLE DieudonneModule DieudonneModule.of DieudonneModule.of_shiftLE DieudonneModule.exists_of"
namespace Stabilisation
p2m_open "Deformation"

open TensorProduct

universe u v

variable (k : Type u) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] [PerfectRing k p]
variable (A : Type v) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]

abbrev B : Type (max u v) := WithConv (A →ₗ[k] k)

omit [CharP k p] [PerfectRing k p] [Coalgebra.IsCocomm k A] [Module.Finite k A] in
theorem one_ofConv_one : (1 : B k A).ofConv 1 = 1 := by
  rw [LinearMap.convOne_apply, Bialgebra.counit_one, map_one]

scoped instance nontrivial_B : Nontrivial (B k A) :=
  ⟨⟨1, 0, fun h => one_ne_zero (α := k) (by
    have := congrArg (fun f : B k A => f.ofConv 1) h
    rwa [one_ofConv_one] at this)⟩⟩

omit hp [PerfectRing k p] [Coalgebra.IsCocomm k A] [Module.Finite k A] in
theorem natCast_p_eq_zero : (p : B k A) = 0 := by
  rw [← nsmul_one]
  apply WithConv.ext
  refine LinearMap.ext fun a => ?_
  change (p : ℕ) • ((1 : B k A).ofConv a) = 0
  rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]

scoped instance charP_B : CharP (B k A) p := (CharP.charP_iff_prime_eq_zero hp.out).2 (natCast_p_eq_zero k p A)

scoped instance isScalarTower_B : IsScalarTower k (B k A) (B k A) where
  smul_assoc c β γ := by
    change c • β * γ = c • (β * γ)
    apply WithConv.ext
    simp only [LinearMap.convMul_def, WithConv.ofConv_toConv, WithConv.ofConv_smul,
      TensorProduct.map_smul_left, LinearMap.smul_comp, LinearMap.comp_smul]

scoped instance smulCommClass_B : SMulCommClass k (B k A) (B k A) where
  smul_comm c β γ := by
    change c • (β * γ) = β * (c • γ)
    apply WithConv.ext
    simp only [LinearMap.convMul_def, WithConv.ofConv_toConv, WithConv.ofConv_smul,
      TensorProduct.map_smul_right, LinearMap.smul_comp, LinearMap.comp_smul]

scoped instance finite_B : Module.Finite k (B k A) :=
  Module.Finite.equiv (WithConv.linearEquiv k (A →ₗ[k] k)).symm

theorem frobeniusEquiv_symm_iterate_pow (j : ℕ) (a : k) :
    ((frobeniusEquiv k p).symm^[j] a) ^ p ^ j = a := by
  induction j generalizing a with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih]
    have h := (frobeniusEquiv k p).apply_symm_apply a
    rwa [frobeniusEquiv_apply] at h

def R (j : ℕ) : Submodule k (B k A) where
  carrier := {b | ∃ c : B k A, c ^ p ^ j = b}
  add_mem' := by
    rintro _ _ ⟨c₁, rfl⟩ ⟨c₂, rfl⟩
    exact ⟨c₁ + c₂, add_pow_char_pow c₁ c₂ p j⟩
  zero_mem' := ⟨0, zero_pow (pow_ne_zero _ hp.out.ne_zero)⟩
  smul_mem' := by
    rintro a _ ⟨c, rfl⟩
    refine ⟨((frobeniusEquiv k p).symm^[j] a) • c, ?_⟩
    rw [smul_pow, frobeniusEquiv_symm_iterate_pow]

omit [Module.Finite k A] in
theorem R_antitone : Antitone (R k p A) := by
  intro i j hij b
  rintro ⟨c, rfl⟩
  exact ⟨c ^ p ^ (j - i), by rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hij]⟩

theorem exists_stable : ∃ N : ℕ, ∀ m, N ≤ m → R k p A N = R k p A m := by
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes
    (⟨fun j => OrderDual.toDual (R k p A j), fun i j hij => R_antitone k p A hij⟩ :
      ℕ →o (Submodule k (B k A))ᵒᵈ)
  exact ⟨N, fun m hm => OrderDual.toDual.injective (hN m hm)⟩

theorem coeff_zero_eq_zero {N : ℕ} (hN : ∀ m, N ≤ m → R k p A N = R k p A m) {n : ℕ} (hn : N < n)
    {x : TruncatedWittVector p n A} (hx : x ∈ wittHom k p n A) :
    x.coeff ⟨0, Nat.zero_lt_of_lt hn⟩ = 0 := by
  have VR := fun β : B k A => Deformation.VerschiebungRelation.main k p A k β hx

  have iter : ∀ (i : ℕ) (hi : i < n) (β : B k A),
      (β ^ p ^ i).ofConv (x.coeff ⟨i, hi⟩) = (β.ofConv (x.coeff ⟨0, Nat.zero_lt_of_lt hi⟩)) ^ p ^ i := by
    intro i
    induction i with
    | zero => intro hi β; simp
    | succ i ih =>
      intro hi β
      rw [pow_succ, pow_mul, (VR (β ^ p ^ i)).2 i hi, ih (Nat.lt_of_succ_lt hi) β, ← pow_mul]
  rw [← Module.forall_dual_apply_eq_zero_iff k]
  intro φ
  let β : B k A := WithConv.toConv φ

  obtain ⟨γ, hγ⟩ : β ^ p ^ N ∈ R k p A (N + 1 + N) := by
    rw [← hN _ (by omega)]
    exact ⟨β, rfl⟩
  have h1 : (γ ^ p ^ (N + 1)).ofConv (x.coeff ⟨0, Nat.zero_lt_of_lt hn⟩) = 0 := by
    have := (VR (γ ^ p ^ N)).1 (Nat.zero_lt_of_lt hn)
    rwa [← pow_mul, ← pow_succ] at this
  have h2 : (β - γ ^ p ^ (N + 1)) ^ p ^ N = 0 := by
    rw [sub_pow_char_pow, ← hγ, ← pow_mul, ← pow_add, sub_self]
  have h3 : (β - γ ^ p ^ (N + 1)).ofConv (x.coeff ⟨0, Nat.zero_lt_of_lt hn⟩) = 0 := by
    have h4 := iter N hn (β - γ ^ p ^ (N + 1))
    rw [h2] at h4
    have h5 : ((β - γ ^ p ^ (N + 1)).ofConv (x.coeff ⟨0, Nat.zero_lt_of_lt hn⟩)) ^ p ^ N = 0 := by
      rw [← h4]; rfl
    exact (pow_eq_zero_iff (pow_ne_zero _ hp.out.ne_zero)).1 h5
  have e : β = γ ^ p ^ (N + 1) + (β - γ ^ p ^ (N + 1)) := by abel
  have h6 : β.ofConv (x.coeff ⟨0, Nat.zero_lt_of_lt hn⟩) = 0 := by
    rw [e, WithConv.ofConv_add, LinearMap.add_apply, h1, h3, add_zero]
  exact h6

theorem coeff_eq_zero {N : ℕ} (hN : ∀ m, N ≤ m → R k p A N = R k p A m) :
    ∀ (n : ℕ) (x : TruncatedWittVector p n A), x ∈ wittHom k p n A →
      ∀ (i : Fin n), (i : ℕ) + N < n → x.coeff i = 0 := by
  intro n
  induction n with
  | zero => intro x _ i; exact i.elim0
  | succ n ih =>
    intro x hx i hi
    have h0 : x.coeff ⟨0, n.succ_pos⟩ = 0 := coeff_zero_eq_zero k p A hN (by omega) hx
    let x' : TruncatedWittVector p n A := TruncatedWittVector.mk p fun j => x.coeff j.succ
    have hx' : TruncWitt.shift x' = x := by
      refine TruncatedWittVector.ext fun j => ?_
      refine Fin.cases ?_ (fun j => ?_) j
      · rw [TruncWitt.coeff_shift_zero]; exact h0.symm
      · rw [TruncWitt.coeff_shift_succ, TruncatedWittVector.coeff_mk]
    have hmem : x' ∈ wittHom k p n A := by
      rw [← shiftLE_mem_wittHom_iff (Nat.le_succ n), TruncWitt.shiftLE_succ, hx']
      exact hx
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro _; exact h0
    · intro hj
      rw [← hx', TruncWitt.coeff_shift_succ, TruncatedWittVector.coeff_mk]
      exact ih x' hmem j (by rw [Fin.val_succ] at hj; omega)

theorem exists_surjective_of : ∃ N : ℕ, Function.Surjective (DieudonneModule.of k p A N) := by
  obtain ⟨N, hN⟩ := exists_stable k p A
  refine ⟨N, fun z => ?_⟩
  obtain ⟨n, x, rfl⟩ := DieudonneModule.exists_of z
  rcases le_total n N with h | h
  · exact ⟨wittHomShiftLE k p A h x, DieudonneModule.of_shiftLE h x⟩
  · let y : TruncatedWittVector p N A :=
      TruncatedWittVector.mk p fun i => (x : TruncatedWittVector p n A).coeff ⟨i + (n - N), by omega⟩
    have hy : TruncWitt.shiftLE h y = x := by
      refine TruncatedWittVector.ext fun i => ?_
      rw [TruncWitt.coeff_shiftLE]
      split_ifs with hi
      · rw [TruncatedWittVector.coeff_mk]
        congr 1
        ext
        simp only
        omega
      · exact (coeff_eq_zero k p A hN n x x.2 i (by omega)).symm
    have hymem : y ∈ wittHom k p N A := by
      rw [← shiftLE_mem_wittHom_iff h, hy]; exact x.2
    refine ⟨⟨y, hymem⟩, ?_⟩
    rw [← DieudonneModule.of_shiftLE h ⟨y, hymem⟩]
    congr 1
    exact Subtype.ext hy

end Deformation.Stabilisation
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation.VerschiebungRelation.Univ P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation.VerschiebungRelation P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation.Stabilisation"
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation.VerschiebungRelation.Univ P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation P2MW.S_Deformation_DieudonneModule_exists_surjective_of.Deformation.VerschiebungRelation"

universe u v in

theorem solution
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (A : Type v) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A] :
    ∃ N : ℕ, Function.Surjective (Deformation.DieudonneModule.of k p A N) :=
  Deformation.Stabilisation.exists_surjective_of k p A

end S_Deformation_DieudonneModule_exists_surjective_of
end P2MW
export P2MW.S_Deformation_DieudonneModule_exists_surjective_of (solution)
