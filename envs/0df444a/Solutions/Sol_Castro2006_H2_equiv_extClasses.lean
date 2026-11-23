-- Prove2me | solution 1 for Castro2006.H2_equiv_extClasses
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T09:10:07.938376+00:00
-- url     : https://prove2.me/submissions/a3f108c4-9da1-4135-83ab-96e05e2b42b2

import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Definitions.Def_Castro2006_action
import Definitions.Def_Castro2006_extQuot
open CategoryTheory

namespace Castro2006GCH2

open groupCohomology Castro2006

variable {G N : Type} [Group G] [CommGroup N] (φ : G →* MulAut N)

/-! ### Cocycle conditions written with `φ` -/

/-- Multiplicative 2-cocycle condition for the action `φ`. -/
def IsCoc (f : G × G → N) : Prop :=
  ∀ g h j : G, f (g * h, j) * f (g, h) = φ g (f (h, j)) * f (g, h * j)

/-- Multiplicative 2-coboundary condition for the action `φ`. -/
def IsCob (f : G × G → N) : Prop :=
  ∃ x : G → N, ∀ g h : G, φ g (x h) / x (g * h) * x g = f (g, h)

variable {φ}

theorem IsCoc.one_fst {f : G × G → N} (hf : IsCoc φ f) (g : G) : f (1, g) = f (1, 1) := by
  have := hf 1 1 g
  simp only [one_mul, map_one, MulAut.one_apply] at this
  exact (mul_left_cancel this).symm

theorem IsCoc.one_snd {f : G × G → N} (hf : IsCoc φ f) (g : G) :
    f (g, 1) = φ g (f (1, 1)) := by
  have := hf g 1 1
  simp only [mul_one] at this
  exact mul_right_cancel this

/-- The element of `Z²` attached to a multiplicative cocycle. -/
def toZ (f : G × G → N) (hf : IsCoc φ f) : cocycles₂ (repOfMulAut φ) :=
  ⟨fun p => Additive.ofMul (f p), (mem_cocycles₂_iff _).2 (fun g h j => hf g h j)⟩

theorem toZ_congr {f f' : G × G → N} (hf : IsCoc φ f) (hf' : IsCoc φ f') (h : f = f') :
    toZ f hf = toZ f' hf' := by
  subst h; rfl

theorem H2π_toZ_eq_of_isCob {f f' : G × G → N} (hf : IsCoc φ f) (hf' : IsCoc φ f')
    (h : IsCob φ (fun p => f p / f' p)) :
    H2π (repOfMulAut φ) (toZ f hf) = H2π (repOfMulAut φ) (toZ f' hf') := by
  rw [H2π_eq_iff]
  obtain ⟨x, hx⟩ := h
  refine ⟨fun g => Additive.ofMul (x g), ?_⟩
  funext p
  exact hx p.1 p.2

theorem isCob_of_H2π_toZ_eq {f f' : G × G → N} (hf : IsCoc φ f) (hf' : IsCoc φ f')
    (h : H2π (repOfMulAut φ) (toZ f hf) = H2π (repOfMulAut φ) (toZ f' hf')) :
    IsCob φ (fun p => f p / f' p) := by
  rw [H2π_eq_iff] at h
  obtain ⟨x, hx⟩ := h
  refine ⟨fun g => Additive.toMul (x g), fun g h => ?_⟩
  exact congrFun hx (g, h)

/-! ### Extensions and sections -/

section Ext

variable {E : Type} [Group E] (S : GroupExtension N E G)

theorem inducedAct_rightHom (e : E) : inducedAct S (S.rightHom e) = S.conjAct e := by
  have : S.quotientRangeInlEquivRight.symm (S.rightHom e) =
      (QuotientGroup.mk e : E ⧸ S.inl.range) := by
    rw [MulEquiv.symm_apply_eq]; rfl
  simp only [inducedAct, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this]
  rfl

variable {S}

theorem inl_act (hS : inducedAct S = φ) (e : E) (n : N) :
    S.inl (φ (S.rightHom e) n) = e * S.inl n * e⁻¹ := by
  rw [← hS, inducedAct_rightHom, S.inl_conjAct_comm]

theorem mul_inl (hS : inducedAct S = φ) (e : E) (n : N) :
    e * S.inl n = S.inl (φ (S.rightHom e) n) * e := by
  rw [inl_act hS]; group

variable {σ : G → E} (hσ : ∀ g, S.rightHom (σ g) = g)
include hσ

theorem mem_range (g h : G) : σ g * σ h * (σ (g * h))⁻¹ ∈ S.inl.range := by
  rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
  simp [hσ]

/-- The 2-cocycle of an extension with respect to a set-theoretic section. -/
noncomputable def cocyc (p : G × G) : N := Classical.choose (mem_range hσ p.1 p.2)

theorem inl_cocyc (g h : G) : S.inl (cocyc hσ (g, h)) = σ g * σ h * (σ (g * h))⁻¹ :=
  Classical.choose_spec (mem_range hσ g h)

theorem sec_mul (g h : G) : σ g * σ h = S.inl (cocyc hσ (g, h)) * σ (g * h) := by
  rw [inl_cocyc]; group

theorem isCoc_cocyc (hS : inducedAct S = φ) : IsCoc φ (cocyc hσ) := by
  intro g h j
  apply S.inl_injective
  have e1 : σ g * σ h * σ j = S.inl (cocyc hσ (g, h) * cocyc hσ (g * h, j)) * σ (g * h * j) := by
    rw [sec_mul hσ g h, mul_assoc, sec_mul hσ, map_mul]; simp only [mul_assoc]
  have e2 : σ g * σ h * σ j =
      S.inl (φ g (cocyc hσ (h, j)) * cocyc hσ (g, h * j)) * σ (g * h * j) := by
    rw [mul_assoc, sec_mul hσ h j, ← mul_assoc, mul_inl hS, hσ, mul_assoc, sec_mul hσ, map_mul,
      mul_assoc, mul_assoc]
  have := e1.symm.trans e2
  rw [mul_left_inj, mul_comm] at this
  rw [this]

theorem cocyc_one : S.inl (cocyc hσ (1, 1)) = σ 1 := by
  rw [inl_cocyc]; simp

/-- Change of section by `x : G → N`. -/
theorem cocyc_change (hS : inducedAct S = φ) (x : G → N) {σ' : G → E}
    (hσ' : ∀ g, S.rightHom (σ' g) = g) (hx : ∀ g, σ' g = S.inl (x g) * σ g) (g h : G) :
    cocyc hσ' (g, h) = x g * φ g (x h) * cocyc hσ (g, h) * (x (g * h))⁻¹ := by
  apply S.inl_injective
  rw [inl_cocyc, hx, hx, hx]
  have : σ g * S.inl (x h) = S.inl (φ g (x h)) * σ g := by rw [mul_inl hS, hσ]
  calc S.inl (x g) * σ g * (S.inl (x h) * σ h) * (S.inl (x (g * h)) * σ (g * h))⁻¹
      = S.inl (x g) * (σ g * S.inl (x h)) * σ h * (σ (g * h))⁻¹ * (S.inl (x (g * h)))⁻¹ := by
        group
    _ = S.inl (x g) * S.inl (φ g (x h)) * (σ g * σ h * (σ (g * h))⁻¹) *
          (S.inl (x (g * h)))⁻¹ := by rw [this]; group
    _ = _ := by rw [← inl_cocyc hσ]; simp only [map_mul, map_inv]

theorem isCob_change (hS : inducedAct S = φ) {σ' : G → E}
    (hσ' : ∀ g, S.rightHom (σ' g) = g) :
    IsCob φ (fun p => cocyc hσ' p / cocyc hσ p) := by
  have hmem : ∀ g, σ' g * (σ g)⁻¹ ∈ S.inl.range := fun g => by
    rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]; simp [hσ, hσ']
  choose x hx using hmem
  have hx' : ∀ g, σ' g = S.inl (x g) * σ g := fun g => by rw [hx]; group
  refine ⟨x, fun g h => ?_⟩
  show _ = cocyc hσ' (g, h) / cocyc hσ (g, h)
  rw [cocyc_change hσ hS x hσ' hx']
  simp [div_eq_mul_inv, mul_comm, mul_left_comm]

/-- Transport of a section along an equivalence of extensions preserves the cocycle. -/
theorem cocyc_equiv {E' : Type} [Group E'] {S' : GroupExtension N E' G} (e : S.Equiv S')
    (he : ∀ g, S'.rightHom (e (σ g)) = g) : cocyc he = cocyc hσ := by
  funext p
  apply S'.inl_injective
  rw [inl_cocyc, ← e.map_inl, inl_cocyc]
  simp only [map_mul, map_inv]

end Ext

/-! ### The crossed-product extension attached to a cocycle -/

/-- Cocycles for `φ`. -/
abbrev Z (φ : G →* MulAut N) : Type := {f : G × G → N // IsCoc φ f}

/-- The crossed product `N ×_f G` as a type. -/
@[nolint unusedArguments]
def CT (φ : G →* MulAut N) (_f : Z φ) : Type := N × G

namespace CT

variable {f : Z φ}

/-- Constructor. -/
def mk (n : N) (g : G) : CT φ f := (n, g)
/-- First component. -/
def n (x : CT φ f) : N := Prod.fst (α := N) (β := G) x
/-- Second component. -/
def g (x : CT φ f) : G := Prod.snd (α := N) (β := G) x

@[simp] theorem n_mk (a : N) (b : G) : (mk a b : CT φ f).n = a := rfl
@[simp] theorem g_mk (a : N) (b : G) : (mk a b : CT φ f).g = b := rfl
theorem ext' {x y : CT φ f} (h1 : x.n = y.n) (h2 : x.g = y.g) : x = y := Prod.ext h1 h2
theorem eta (x : CT φ f) : mk x.n x.g = x := rfl

instance : Mul (CT φ f) := ⟨fun x y => mk (x.n * φ x.g y.n * f.1 (x.g, y.g)) (x.g * y.g)⟩
instance : One (CT φ f) := ⟨mk (f.1 (1, 1))⁻¹ 1⟩
instance : Inv (CT φ f) :=
  ⟨fun x => mk ((f.1 (1, 1))⁻¹ * (φ x.g⁻¹ x.n)⁻¹ * (f.1 (x.g⁻¹, x.g))⁻¹) x.g⁻¹⟩

@[simp] theorem mul_n (x y : CT φ f) : (x * y).n = x.n * φ x.g y.n * f.1 (x.g, y.g) := rfl
@[simp] theorem mul_g (x y : CT φ f) : (x * y).g = x.g * y.g := rfl
@[simp] theorem one_n : (1 : CT φ f).n = (f.1 (1, 1))⁻¹ := rfl
@[simp] theorem one_g : (1 : CT φ f).g = 1 := rfl
@[simp] theorem inv_n (x : CT φ f) :
    (x⁻¹).n = (f.1 (1, 1))⁻¹ * (φ x.g⁻¹ x.n)⁻¹ * (f.1 (x.g⁻¹, x.g))⁻¹ := rfl
@[simp] theorem inv_g (x : CT φ f) : (x⁻¹).g = x.g⁻¹ := rfl

instance : Group (CT φ f) := Group.ofLeftAxioms
  (fun x y z => by
    apply ext'
    · have key := f.2 x.g y.g z.g
      simp only [mul_n, mul_g, map_mul, MulAut.mul_apply]
      calc x.n * φ x.g y.n * f.1 (x.g, y.g) * (φ x.g (φ y.g z.n)) * f.1 (x.g * y.g, z.g)
          = x.n * φ x.g y.n * φ x.g (φ y.g z.n) * (f.1 (x.g * y.g, z.g) * f.1 (x.g, y.g)) := by
            simp only [mul_comm, mul_left_comm, mul_assoc]
        _ = _ := by rw [key]; simp only [mul_comm, mul_left_comm]
    · simp [mul_assoc])
  (fun x => by
    apply ext'
    · simp [f.2.one_fst]
    · simp)
  (fun x => by
    apply ext'
    · simp only [mul_n, inv_n, inv_g, one_n]
      simp [mul_comm, mul_left_comm]
    · simp)

/-- The extension `1 → N → N ×_f G → G → 1`. -/
noncomputable def ext (f : Z φ) : GroupExtension N (CT φ f) G where
  inl :=
    { toFun := fun a => mk (a * (f.1 (1, 1))⁻¹) 1
      map_one' := by apply ext' <;> simp
      map_mul' := fun a b => by
        apply ext'
        · simp [mul_comm, mul_left_comm, mul_assoc]
        · simp }
  rightHom :=
    { toFun := fun x => x.g
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  inl_injective := fun a b h => by
    have := congrArg CT.n h
    simpa using this
  range_inl_eq_ker_rightHom := by
    ext x
    simp only [MonoidHom.mem_range, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.mem_ker]
    constructor
    · rintro ⟨a, rfl⟩; rfl
    · intro hx
      exact ⟨x.n * f.1 (1, 1), ext' (by simp) (by exact hx.symm)⟩
  rightHom_surjective := fun b => ⟨mk 1 b, rfl⟩

theorem ext_rightHom (x : CT φ f) : (ext f).rightHom x = x.g := rfl
theorem ext_inl (a : N) : (ext f).inl a = mk (a * (f.1 (1, 1))⁻¹) 1 := rfl

/-- The canonical section. -/
def sec (f : Z φ) (b : G) : CT φ f := mk 1 b

theorem sec_spec : ∀ b, (ext f).rightHom (sec f b) = b := fun _ => rfl

theorem cocyc_sec : cocyc (sec_spec (f := f)) = f.1 := by
  funext p
  obtain ⟨a, b⟩ := p
  apply (ext f).inl_injective
  rw [inl_cocyc, mul_inv_eq_iff_eq_mul]
  apply ext'
  · simp [ext_inl, sec, f.2.one_fst]
  · simp [ext_inl, sec]

theorem ext_induces : inducedAct (ext f) = φ := by
  ext b a
  have h1 := inducedAct_rightHom (ext f) (sec f b)
  rw [show (ext f).rightHom (sec f b) = b from rfl] at h1
  rw [h1]
  apply (ext f).inl_injective
  rw [GroupExtension.inl_conjAct_comm, mul_inv_eq_iff_eq_mul]
  apply ext'
  · simp only [mul_n, ext_inl, sec, n_mk, g_mk, map_mul, map_inv, f.2.one_fst]
    rw [f.2.one_snd b]
    simp
  · simp [ext_inl, sec]

end CT

/-- Every extension with a section is equivalent to the crossed product of its cocycle. -/
noncomputable def equivCT {E : Type} [Group E] {S : GroupExtension N E G}
    (hS : inducedAct S = φ) {σ : G → E} (hσ : ∀ g, S.rightHom (σ g) = g) (f : Z φ)
    (hf : f.1 = cocyc hσ) : (CT.ext f).Equiv S :=
  GroupExtension.Equiv.ofMonoidHom
    { toFun := fun x => S.inl x.n * σ x.g
      map_one' := by
        simp only [CT.one_n, CT.one_g, hf, map_inv, cocyc_one]
        group
      map_mul' := fun x y => by
        simp only [CT.mul_n, CT.mul_g, map_mul, hf]
        rw [show S.inl x.n * σ x.g * (S.inl y.n * σ y.g) =
          S.inl x.n * (σ x.g * S.inl y.n) * σ y.g by group, mul_inl hS (σ x.g) y.n, hσ]
        simp only [mul_assoc, sec_mul hσ] }
    (by
      ext a
      simp only [MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk, CT.ext_inl, CT.n_mk,
        CT.g_mk, map_mul, map_inv, hf, cocyc_one]
      group)
    (by
      ext x
      simp [CT.ext_rightHom, hσ])

/-- Two extensions with sections having the same cocycle are equivalent. -/
theorem equiv_of_cocyc_eq {E E' : Type} [Group E] [Group E'] {S : GroupExtension N E G}
    {S' : GroupExtension N E' G} (hS : inducedAct S = φ) (hS' : inducedAct S' = φ)
    {σ : G → E} (hσ : ∀ g, S.rightHom (σ g) = g) {σ' : G → E'}
    (hσ' : ∀ g, S'.rightHom (σ' g) = g) (h : cocyc hσ = cocyc hσ') : Nonempty (S.Equiv S') :=
  ⟨((equivCT hS hσ ⟨_, isCoc_cocyc hσ hS⟩ rfl).symm).trans
    (equivCT hS' hσ' ⟨_, isCoc_cocyc hσ hS⟩ h)⟩

/-! ### The map `ExtClasses φ → H²` -/

attribute [local instance] ExtOf.grp

/-- The cohomology class of an extension. -/
noncomputable def cls (x : ExtOf φ) : H2 (repOfMulAut φ) :=
  H2π (repOfMulAut φ) (toZ _ (isCoc_cocyc (S := x.S) (Function.surjInv_eq x.S.rightHom_surjective)
    x.induces))

theorem cls_eq (x : ExtOf φ) {σ : G → x.E} (hσ : ∀ g, x.S.rightHom (σ g) = g) :
    cls x = H2π (repOfMulAut φ) (toZ _ (isCoc_cocyc hσ x.induces)) := by
  apply H2π_toZ_eq_of_isCob
  exact isCob_change hσ x.induces _

theorem cls_wd (x y : ExtOf φ) (h : ExtRel φ x y) : cls x = cls y := by
  obtain ⟨e⟩ := h
  have hσ := Function.surjInv_eq x.S.rightHom_surjective
  have he : ∀ g, y.S.rightHom (e (Function.surjInv x.S.rightHom_surjective g)) = g := fun g => by
    rw [e.rightHom_map, hσ]
  rw [cls_eq x hσ, cls_eq y he]
  exact congrArg _ (toZ_congr _ _ (cocyc_equiv hσ e he).symm)

/-- The map on classes. -/
noncomputable def F : ExtClasses φ → H2 (repOfMulAut φ) :=
  Quotient.lift (s := extSetoid φ) cls cls_wd

theorem F_injective : Function.Injective (F (φ := φ)) := by
  intro a b
  induction a using Quotient.inductionOn with | _ x => ?_
  induction b using Quotient.inductionOn with | _ y => ?_
  intro h
  change cls x = cls y at h
  apply Quotient.sound
  change ExtRel φ x y
  unfold cls at h
  have hσx := Function.surjInv_eq x.S.rightHom_surjective
  have hσy := Function.surjInv_eq y.S.rightHom_surjective
  obtain ⟨w, hw⟩ := isCob_of_H2π_toZ_eq _ _ h
  let σ' : G → y.E := fun g => y.S.inl (w g) * Function.surjInv y.S.rightHom_surjective g
  have hσ' : ∀ g, y.S.rightHom (σ' g) = g := fun g => by simp [σ', hσy]
  have hc := cocyc_change hσy y.induces w hσ' (fun g => rfl)
  refine equiv_of_cocyc_eq x.induces y.induces hσx hσ' ?_
  funext p
  obtain ⟨g, h⟩ := p
  rw [hc]
  have := hw g h
  simp only at this
  rw [eq_div_iff_mul_eq'] at this
  rw [← this]
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

theorem F_surjective : Function.Surjective (F (φ := φ)) := by
  intro y
  induction y using H2_induction_on with | h z => ?_
  have hf : IsCoc φ (fun p => Additive.toMul (z p)) := fun g h j =>
    (mem_cocycles₂_iff _).1 z.2 g h j
  let f : Z φ := ⟨_, hf⟩
  refine ⟨Quotient.mk (extSetoid φ) ⟨CT φ f, CT.ext f, CT.ext_induces⟩, ?_⟩
  change cls _ = _
  rw [cls_eq _ CT.sec_spec]
  congr 1
  rw [toZ_congr _ hf CT.cocyc_sec]
  rfl

end Castro2006GCH2

open Castro2006 in
theorem solution {G N : Type} [Group G] [CommGroup N] (φ : G →* MulAut N) :
    Nonempty (Castro2006.ExtClasses φ ≃ groupCohomology (Castro2006.repOfMulAut φ) 2) :=
  ⟨Equiv.ofBijective _ ⟨Castro2006GCH2.F_injective, Castro2006GCH2.F_surjective⟩⟩
