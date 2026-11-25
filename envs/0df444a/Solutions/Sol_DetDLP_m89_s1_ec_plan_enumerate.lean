-- Prove2me | solution 1 for DetDLP.m89_s1_ec_plan_enumerate
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T04:50:42.876844+00:00
-- url     : https://prove2.me/submissions/7fd128f9-5019-4de2-b91f-0849640458d4

import Std
import Definitions.Def_DetDLP_M89_S1_Plans
import Definitions.Def_ToTuring_Lib_List2
import Theorems.Thm_DetDLP_hasse_ec_point_count_bound
import Theorems.Thm_DetDLP_stage1_complexity_dominance
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_div
import Theorems.Thm_DetDLP_m89_polyT_oracle_loop
import Theorems.Thm_DetDLP_stage1_cond_exp_derand_and_size_bounds
import Definitions.Def_DetDLP_PolyTBridge

section

set_option autoImplicit false
namespace DetDLP.ECEnumTrie
abbrev W := List Bool

/-- Produces only words with a positive count. Each recursive invocation makes one query. -/
def enumerate (cnt : W → Nat) : Nat → W → List W
  | 0, w => if cnt w = 0 then [] else [w]
  | n+1, w => if cnt w = 0 then [] else
      enumerate cnt n (w ++ [false]) ++ enumerate cnt n (w ++ [true])

def calls (cnt : W → Nat) : Nat → W → Nat
  | 0, _ => 1
  | n+1, w => if cnt w = 0 then 1 else
      1 + calls cnt n (w ++ [false]) + calls cnt n (w ++ [true])

def Additive (cnt : W → Nat) (N : Nat) := ∀ w : W, w.length < N →
  cnt w = cnt (w ++ [false]) + cnt (w ++ [true])

theorem calls_le (cnt : W → Nat) (N : Nat) (mass : Additive cnt N) (n : Nat) (w : W)
    (hn : w.length+n = N) : calls cnt n w ≤ 1+2*n*cnt w := by
  induction n generalizing w with
  | zero => simp [calls]
  | succ n ih =>
    by_cases h : cnt w = 0
    · simp [calls,h]
    · simp only [calls,if_neg h]
      have l := ih (w ++ [false]) (by simp; omega)
      have r := ih (w ++ [true]) (by simp; omega)
      have eq := mass w (by omega)
      have d := congrArg (fun c => 2*n*c) eq
      simp only [Nat.mul_add] at d
      rw [Nat.mul_succ,Nat.add_mul]
      omega

private theorem prefix_of_mem (cnt : W → Nat) (n : Nat) (w v : W)
    (h : v ∈ enumerate cnt n w) : ∃ t : W, v = w ++ t := by
  induction n generalizing w with
  | zero =>
    by_cases e : cnt w = 0 <;> simp_all [enumerate]
  | succ n ih =>
    by_cases e : cnt w = 0
    · simp [enumerate,e] at h
    · simp only [enumerate,if_neg e,List.mem_append] at h
      rcases h with h | h
      · obtain ⟨t,ht⟩ := ih _ h; exact ⟨false::t,by simpa using ht⟩
      · obtain ⟨t,ht⟩ := ih _ h; exact ⟨true::t,by simpa using ht⟩

theorem nodup (cnt : W → Nat) (n : Nat) (w : W) : (enumerate cnt n w).Nodup := by
  induction n generalizing w with
  | zero => by_cases h : cnt w = 0 <;> simp [enumerate,h]
  | succ n ih =>
    by_cases h : cnt w = 0
    · simp [enumerate,h]
    · simp only [enumerate,if_neg h,List.Nodup]
      apply List.pairwise_append.mpr
      refine ⟨ih _, ih _, ?_⟩
      intro l hl r hr he
      obtain ⟨x,hx⟩ := prefix_of_mem _ _ _ _ hl
      obtain ⟨y,hy⟩ := prefix_of_mem _ _ _ _ hr
      simp [hx,hy] at he

theorem enumeration_spec (cnt : W → Nat) (N : Nat) (mass : Additive cnt N)
    (w t : W) (hn : w.length+t.length = N) :
    w ++ t ∈ enumerate cnt t.length w ↔ 0 < cnt (w ++ t) := by
  induction t generalizing w with
  | nil =>
    by_cases h : cnt w = 0 <;> simp [enumerate,h] <;> omega
  | cons bit t ih =>
    have m := mass w (by simp at hn; omega)
    have next := ih (w++[bit]) (by simp at hn ⊢; omega)
    have p := prefix_of_mem cnt t.length
    simp only [List.length_cons,enumerate]
    cases bit <;> simp only [List.append_assoc,List.singleton_append] at next
    all_goals
      split
      · rename_i h
        have : cnt (w++[false]) = 0 ∧ cnt (w++[true]) = 0 := by omega
        cases t <;> simp [enumerate,this] at next ⊢ <;> omega
      · rw [List.mem_append,←next]
        constructor
        · intro h
          first | exact h.resolve_right (fun hy => by obtain ⟨z,hz⟩ := p _ _ hy; simp at hz)
                | exact h.resolve_left (fun hy => by obtain ⟨z,hz⟩ := p _ _ hy; simp at hz)
        · intro h; first | exact Or.inl h | exact Or.inr h

def prefixCount (D : List W) (w : W) : Nat := D.countP (fun x => x.take w.length == w)

private theorem split_bit (x w : W) (h : w.length < x.length) :
    (decide (x.take w.length = w)).toNat =
      (decide (x.take (w.length+1) = w++[false])).toNat +
      (decide (x.take (w.length+1) = w++[true])).toNat := by
  induction w generalizing x with
  | nil => cases x with
           | nil => simp at h
           | cons a x => cases a <;> rfl
  | cons a w ih =>
    cases x with
    | nil => simp at h
    | cons b x =>
      have e := ih x (by simpa using h)
      by_cases hb : b = a
      · subst b; simpa using e
      · simp [hb]

theorem prefixCount_additive (D : List W) (N : Nat) (h : ∀ x ∈ D, x.length = N) :
    Additive (prefixCount D) N := by
  intro w hw
  induction D with
  | nil => rfl
  | cons x D ih =>
    have rest := ih (fun u hu => h u (List.mem_cons_of_mem _ hu))
    have hx : w.length < x.length := by rw [h x (by simp)]; exact hw
    have head := split_bit x w hx
    simp only [prefixCount,List.countP_cons,List.length_append,List.length_cons,List.length_nil] at *
    simp only [Nat.zero_add,beq_iff_eq] at *
    split <;> split <;> split <;> simp_all <;> omega

theorem length_of_mem (cnt : W → Nat) (n : Nat) (w v : W) (h : v ∈ enumerate cnt n w) :
    v.length = w.length+n := by
  induction n generalizing w with
  | zero => by_cases e : cnt w = 0 <;> simp_all [enumerate]
  | succ n ih =>
    by_cases e : cnt w = 0
    · simp [enumerate,e] at h
    · simp [enumerate,e] at h
      rcases h with h | h <;> have := ih _ h <;> simp at this <;> omega

theorem root_spec (D : List W) (N : Nat) (h : ∀ x ∈ D, x.length = N) (v : W) :
    v ∈ enumerate (prefixCount D) N [] ↔ v ∈ D := by
  by_cases len : v.length = N
  · have e := enumeration_spec (prefixCount D) N (prefixCount_additive D N h) [] v (by simp [len])
    simp only [List.nil_append,len] at e
    rw [e]
    simp only [prefixCount,List.countP_pos_iff]
    constructor
    · rintro ⟨x,hx,he⟩
      have hv : x = v := by simpa [len,←h x hx] using he
      simpa [←hv] using hx
    · intro hv; exact ⟨v,hv,by simp⟩
  · constructor
    · intro hv; exact (len (by simpa using length_of_mem _ _ _ _ hv)).elim
    · intro hv; exact (len (h v hv)).elim

theorem root_calls (D : List W) (N : Nat) (h : ∀ x ∈ D, x.length = N) :
    calls (prefixCount D) N [] ≤ 1+2*N*D.length := by
  simpa [prefixCount] using calls_le (prefixCount D) N (prefixCount_additive D N h) N [] (by simp)

/-- A pending job is its remaining depth and its already-fixed prefix. `revOutput` is in reverse visit order. -/
abbrev Job := Nat × W
structure State where
  pending : List Job
  revOutput : List W

/-- The external controller stops on an empty job list. Otherwise it queries the prefix of the first job. -/
def advance (s : State) (answer : Nat) : State :=
  match s.pending with
  | [] => s
  | (n,w)::todo => if answer = 0 then ⟨todo,s.revOutput⟩ else
      match n with
      | 0 => ⟨todo,w::s.revOutput⟩
      | k+1 => ⟨(k,w++[false]) :: (k,w++[true]) :: todo, s.revOutput⟩

def result (cnt : W → Nat) (s : State) :=
  s.revOutput.reverse ++ s.pending.flatMap (fun j => enumerate cnt j.1 j.2)
def budget (cnt : W → Nat) (s : State) :=
  (s.pending.map (fun j => calls cnt j.1 j.2)).sum

theorem transition (cnt : W → Nat) (todo : List Job) (acc : List W) (n : Nat) (w : W) :
    let s : State := ⟨(n,w)::todo,acc⟩
    let s' := advance s (cnt w)
    result cnt s' = result cnt s ∧ budget cnt s' + 1 = budget cnt s := by
  cases n <;> by_cases h : cnt w = 0 <;>
    simp [advance,result,budget,enumerate,calls,h,List.append_assoc] <;> omega

def execute (cnt : W → Nat) : Nat → State → State
  | 0,s => s
  | fuel+1,s => match s.pending with
    | [] => s
    | (_,w)::_ => execute cnt fuel (advance s (cnt w))

theorem execute_spec (cnt : W → Nat) (fuel : Nat) (s : State) (h : budget cnt s ≤ fuel) :
    (execute cnt fuel s).pending = [] ∧ (execute cnt fuel s).revOutput.reverse = result cnt s := by
  induction fuel generalizing s with
  | zero =>
    obtain ⟨tasks,acc⟩ := s
    cases tasks with
    | nil => simp [execute,result]
    | cons j todo =>
      obtain ⟨n,w⟩ := j
      have t := (transition cnt todo acc n w).2
      omega
  | succ fuel ih =>
    obtain ⟨tasks,acc⟩ := s
    cases tasks with
    | nil => simp [execute,result]
    | cons j todo =>
      obtain ⟨n,w⟩ := j
      have t := transition cnt todo acc n w
      simp only [execute]
      have ht := ih (advance ⟨(n,w)::todo,acc⟩ (cnt w)) (by omega)
      exact ⟨ht.1,ht.2.trans t.1⟩

theorem stack_correct (D : List W) (N : Nat) (h : ∀ x ∈ D, x.length = N) :
    let s := execute (prefixCount D) (1+2*N*D.length) ⟨[(N,[])],[]⟩
    s.pending = [] ∧ s.revOutput.reverse.Nodup ∧ ∀ v, v ∈ s.revOutput.reverse ↔ v ∈ D := by
  dsimp only
  have e := execute_spec (prefixCount D) (1+2*N*D.length) ⟨[(N,[])],[]⟩ (by simpa [budget] using root_calls D N h)
  refine ⟨e.1,?_⟩
  rw [e.2]
  simp only [result,List.reverse_nil,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.nil_append]
  exact ⟨nodup _ _ _,root_spec D N h⟩

end DetDLP.ECEnumTrie

end

section
set_option autoImplicit false
namespace DetDLP.ECEnumDigits

/-- `M89S1.digitWord` without any Mathlib dependencies. -/
def digits (b n : Nat) := List.ofFn (fun i : Fin b => n.testBit i.rev.val)

def fromLE : List Bool → Nat
  | [] => 0
  | a::t => a.toNat + 2 * fromLE t

theorem reverse_digits (b n : Nat) : (digits b n).reverse = List.ofFn (fun i : Fin b => n.testBit i.val) := by
  apply List.ext_getElem (by simp [digits]); intro j hj hk
  simp only [digits,List.getElem_reverse,List.getElem_ofFn,List.length_ofFn,Fin.val_rev]
  congr 1; simp only [List.length_ofFn] at hk; omega

theorem decode (b n : Nat) (hn : n < 2^b) : fromLE (digits b n).reverse = n := by
  rw [reverse_digits]
  induction b generalizing n with
  | zero => simp at hn; subst n; rfl
  | succ b ih =>
    rw [List.ofFn_succ,fromLE]
    simp only [Fin.val_zero,Fin.val_succ,Nat.testBit_succ]
    rw [ih (n/2) (by rw [Nat.pow_succ] at hn; omega),Nat.testBit_zero]
    by_cases h : n%2 = 1 <;> simp [h] <;> omega

theorem inj (b x y : Nat) (hx : x < 2^b) (hy : y < 2^b) (h : digits b x = digits b y) : x = y := by
  rw [←decode b x hx,h,decode b y hy]

end DetDLP.ECEnumDigits

end

section

set_option autoImplicit false
namespace DetDLP.ECEnumSemantic
open M89S1 ECEnumTrie ECEnumDigits
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem threshold_le (p m g : ℕ) (hm : 2 ≤ m) (h64 : 64 ≤ g) (h4096 : 4096*m ≤ g-1) :
    hashThreshold p (g-1) m g ≤ p := by
  let n := g-1
  have hn : (63:ℝ) ≤ (n:ℝ) := by exact_mod_cast (show 63 ≤ n by dsimp [n]; omega)
  have hg : (g:ℝ) = (n:ℝ)+1 := by exact_mod_cast (show g = n+1 by dsimp [n]; omega)
  have hpos : 0 < (n:ℝ) := by linarith
  have he : (1:ℝ)/(m:ℝ) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hm)
  have h16 : (16*(g:ℝ))^((1:ℝ)/(m:ℝ)) ≤ (n:ℝ) := by
    calc
      _ ≤ (16*(g:ℝ))^((1:ℝ)/2) := Real.rpow_le_rpow_of_exponent_le (by linarith) he
      _ ≤ ((n:ℝ)^2)^((1:ℝ)/2) := Real.rpow_le_rpow (by positivity) (by nlinarith [mul_nonneg (by linarith : 0 ≤ (n:ℝ)-32) (by linarith : 0 ≤ (n:ℝ)-1)]) (by norm_num)
      _ = _ := by rw [← Real.rpow_natCast_mul hpos.le]; norm_num
  have hq : qStar m g ≤ n := max_le h4096 (Nat.ceil_le.mpr h16)
  apply Nat.ceil_le.mpr
  exact (div_le_iff₀ hpos).mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast hq) (by positivity))

variable {p : ℕ} [Fact p.Prime] {E : WeierstrassCurve (ZMod p)}

abbrev code := @ecWord p _ E (bitLen p)
def coords (b : ℕ) (w : W) : List ℕ :=
  [(w.headD false).toNat, fromLE (w.tail.take b).reverse, fromLE (w.tail.drop b).reverse]

@[simp] theorem digits_len (b n : ℕ) : (digitWord b n).length = b := List.length_ofFn

theorem coords_code (P : E.toAffine.Point) : coords (bitLen p) (code P) = pointCoords P := by
  have val (n : ℕ) (hn : n < 2^(bitLen p)) : fromLE (digitWord (bitLen p) n).reverse = n := decode _ _ hn
  have len (x y : ℕ) : (digitWord (bitLen p) x ++ digitWord (bitLen p) y).take (bitLen p) = digitWord (bitLen p) x := by
    simpa only [digits_len] using List.take_left (l₁ := digitWord (bitLen p) x) (l₂ := digitWord (bitLen p) y)
  have dr (x y : ℕ) : (digitWord (bitLen p) x ++ digitWord (bitLen p) y).drop (bitLen p) = digitWord (bitLen p) y := by
    simpa only [digits_len] using List.drop_left (l₁ := digitWord (bitLen p) x) (l₂ := digitWord (bitLen p) y)
  cases P with
  | zero => simp [coords,code,ecWord,pointCoords,len,dr,val 0 (by positivity)]
  | some x y _ => simp [coords,code,ecWord,pointCoords,len,dr,val x.val (x.val_lt.trans_le (Nat.le_pow_clog (by decide) p)),val y.val (y.val_lt.trans_le (Nat.le_pow_clog (by decide) p))]

theorem code_inj : Function.Injective (@code p _ E) := by
  intro x y h
  have e := congrArg (coords (bitLen p)) h
  rw [coords_code,coords_code] at e
  cases x <;> cases y <;> simp_all [pointCoords]
  exact ⟨ZMod.val_injective _ e.1, ZMod.val_injective _ e.2⟩

theorem count_eq (D : Finset E.toAffine.Point) : elemCount D code = prefixCount (D.toList.map code) := by
  classical
  funext w
  let P := fun x : E.toAffine.Point => (code x).take w.length = w
  have h := (Finset.nodup_toList D).card_eq_countP (P := P)
  have eq (x y : W) : (x == y) = decide (x = y) := by by_cases hx : x = y <;> simp [hx]
  simpa [elemCount,prefixCount,List.countP_map,P,Function.comp_def,eq] using h

theorem code_len (P : E.toAffine.Point) : (code P).length = 2*bitLen p+1 := by
  cases P <;> simp [code,ecWord] <;> omega

theorem encoded_block (D : Finset E.toAffine.Point) :
    let N := 2*bitLen p+1
    let cnt := elemCount D code
    let Fw := (execute cnt (1+2*N*D.card) ⟨[(N,[])],[]⟩).revOutput.reverse
    ∃ F : List E.toAffine.Point, F.Nodup ∧ F.toFinset = D ∧ F.map code = Fw := by
  classical
  intro N cnt Fw
  let DW := D.toList.map code
  have len : ∀ w ∈ DW, w.length = N := by intro w hw; obtain ⟨P,_,rfl⟩ := List.mem_map.mp hw; exact code_len P
  have spec := stack_correct DW N len
  have hW : Fw.Nodup ∧ ∀ v, v ∈ Fw ↔ v ∈ DW := by
    simpa [Fw,cnt,count_eq,DW] using spec.2
  let get (w : W) : E.toAffine.Point := if e : ∃ P : E.toAffine.Point, code P = w then e.choose else 0
  have get_ok (w : W) (hw : w ∈ Fw) : code (get w) = w := by
    obtain ⟨P,_,he⟩ := List.mem_map.mp ((hW.2 w).mp hw)
    have ex : ∃ Q : E.toAffine.Point, code Q = w := ⟨P,he⟩
    simpa only [get,dif_pos ex] using ex.choose_spec
  refine ⟨Fw.map get,List.Nodup.map_on (fun w hw v hv eq => (get_ok w hw).symm.trans ((congrArg code eq).trans (get_ok v hv))) hW.1,?_,?_⟩
  · ext P
    simp only [List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨w,hw,rfl⟩
      obtain ⟨Q,hQ,he⟩ := List.mem_map.mp ((hW.2 w).mp hw)
      have e := code_inj ((get_ok w hw).trans he.symm)
      simpa [e] using hQ
    · intro hp
      have hw : code P ∈ Fw := (hW.2 _).mpr (List.mem_map.mpr ⟨P,by simpa using hp,rfl⟩)
      exact ⟨_,hw,code_inj (get_ok _ hw)⟩
  · rw [List.map_map]; exact List.map_congr_left (fun w hw => get_ok w hw) |>.trans (List.map_id _)

theorem ec_query (hp : 3 < p) [E.IsElliptic] {T : ℕ} {S : ECSeed p (blockCount (bitLen p))}
    (hok : m89_ec_plan_ok E (some (T,S))) (i : Fin (blockCount (bitLen p))) (w : W) (hlen : w.length ≤ 2*bitLen p+1) :
    Query (queryWord 4 (encodeCurveInput p E) [countWord T,List.ofFn (ecBits S),countWord i.val,w]) (bitLen p) (elemCount (ecFactorBlock E T S i) code w) := by
  obtain ⟨h1,h2,h3,_⟩ := hok
  exact Query.ecElem p hp E T (h3 ▸ threshold_le p _ _ (le_max_left ..) h1 h2) S i w hlen

end DetDLP.ECEnumSemantic

end

section

set_option autoImplicit false
open DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

namespace DetDLP.ECEnumSmall

private theorem blocks_le (b : ℕ) : blockCount b ≤ b+2 := by
  apply max_le (by omega) (Nat.ceil_le.mpr ?_)
  have u : Nat.clog 2 (b+2) ≤ b+2 := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 (Nat.lt_pow_self (by decide)).le
  have v : 1 ≤ Nat.clog 2 (b+2) := Nat.clog_pos (by decide) (by omega)
  exact (Real.rpow_le_self_of_one_le (by exact_mod_cast v) (by norm_num)).trans (by exact_mod_cast u)

private theorem growth (b : ℕ) (hb : 20 ≤ b) : 8192*(b+2)+4 ≤ 2^(b-1) := by
  induction b, hb using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have h : k+1-1 = (k-1)+1 := by omega
    rw [h, pow_succ]
    omega

private theorem prime_bound (p g : ℕ) (hg : p ≤ 2*g+4)
    (hs : ¬ (64 ≤ g ∧ 4096 * blockCount (bitLen p) ≤ g-1)) : p ≤ 2^20 := by
  let b := bitLen p
  have hm : 2 ≤ blockCount b := le_max_left ..
  change ¬(64 ≤ g ∧ 4096 * blockCount b ≤ g-1) at hs
  have hn : g ≤ 4096 * blockCount b := by by_contra! hn; apply hs; constructor <;> omega
  have h : p ≤ 8192*(b+2)+4 := by have := blocks_le b; omega
  have hl : b ≤ 20 := by
    by_contra! hl
    have hu : 2^(b-1) < p := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).1 (show b-1 < b by omega)
    have := growth b (by omega)
    omega
  exact (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).1 hl

private theorem ec_small_bound {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (hsmall : letI := ecPointFintype E; let g := Fintype.card E.toAffine.Point
      ¬(64 ≤ g ∧ 4096 * blockCount (bitLen p) ≤ g-1)) : p ≤ 2^20 := by
  letI := ecPointFintype E
  let g := Fintype.card E.toAffine.Point
  apply prime_bound p g _ hsmall
  have lower := (abs_le.mp (hasse_ec_point_count_bound p hp E)).1
  change -(2 * √(p : ℝ)) ≤ (g : ℝ) - ((p : ℝ) + 1) at lower
  have sq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) p)
  have aux : (p : ℝ) ≤ 2*(g : ℝ)+4 := by nlinarith [sq_nonneg (√(p : ℝ)-2)]
  exact_mod_cast aux

private theorem frame_inj (a b r s : List Bool) (h : Encoding.frame a ++ r = Encoding.frame b ++ s) :
    a = b ∧ r = s := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [Encoding.frame]
  | cons x a ih =>
    cases b with
    | nil => simp [Encoding.frame] at h
    | cons y b =>
      change true :: x :: (Encoding.frame a ++ r) = true :: y :: (Encoding.frame b ++ s) at h
      simp only [List.cons.injEq, true_and] at h
      obtain ⟨ha, hr⟩ := ih b h.2
      exact ⟨congrArg₂ List.cons h.1 ha, hr⟩

private theorem list_inj {α : Type} {enc : α → List Bool} (he : Function.Injective enc) :
    Function.Injective (Encoding.encodeList enc) := by
  intro a b h
  induction a generalizing b with
  | nil => cases b <;> simp_all [Encoding.encodeList]
  | cons x a ih =>
    cases b with
    | nil => simp [Encoding.encodeList] at h
    | cons y b =>
      change true :: (Encoding.frame (enc x) ++ Encoding.encodeList enc a) = true :: (Encoding.frame (enc y) ++ Encoding.encodeList enc b) at h
      obtain ⟨hxy, hab⟩ := frame_inj _ _ _ _ (List.cons.inj h).2
      exact congrArg₂ List.cons (he hxy) (ih hab)

private theorem count_inj : Function.Injective countWord := by
  let dec (w : List Bool) := Nat.ofDigits 2 (w.map Bool.toNat)
  have hdec (n : ℕ) : dec (countWord n) = n := by
    by_cases hn : n = 0
    · subst n; rfl
    · have hd : Nat.digits 2 n = n.bits.map Bool.toNat := by
        rw [Nat.digits_two_eq_bits]
        induction n.bits with
        | nil => rfl
        | cons b v ih => cases b <;> simp_all
      simpa [dec, countWord, hn, ← hd] using Nat.ofDigits_digits 2 n
  exact Function.LeftInverse.injective hdec

private abbrev Pr := {q : Fin (2^20 + 1) // q.val.Prime}
private instance (q : Pr) : Fact q.val.val.Prime := ⟨q.property⟩
private abbrev field (q : Pr) := ZMod q.val.val
private theorem pr_eq {i j : Pr} (h : i.val.val = j.val.val) : i = j := Subtype.ext (Fin.ext h)

private noncomputable def groupBlock {G : Type} [Fintype G] (m : ℕ) : Fin m → List G := fun _ => Finset.univ.toList
private instance (q : Pr) : Finite (WeierstrassCurve (field q)) :=
  Finite.of_injective (fun E => (E.a₁,E.a₂,E.a₃,E.a₄,E.a₆) : WeierstrassCurve (field q) → _)
    (by intro E F h; simp only [Prod.mk.injEq] at h; exact WeierstrassCurve.ext h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)

private abbrev curves := (q : Pr) × WeierstrassCurve (field q)
private abbrev curvePts (c : curves) := c.2.toAffine.Point
private noncomputable instance (c : curves) : Fintype (curvePts c) := ecPointFintype c.2
private def curveInput (c : curves) := encodeCurveInput c.1.val.val c.2
private theorem curve_inj : Function.Injective curveInput := by
  rintro ⟨q,E⟩ ⟨r,F⟩ h
  have he := list_inj count_inj h
  change [q.val.val,E.a₁.val,E.a₂.val,E.a₃.val,E.a₄.val,E.a₆.val] = [r.val.val,F.a₁.val,F.a₂.val,F.a₃.val,F.a₄.val,F.a₆.val] at he
  simp only [List.cons.injEq] at he
  obtain rfl := pr_eq he.1
  have eqEF := WeierstrassCurve.ext (ZMod.val_injective _ he.2.1) (ZMod.val_injective _ he.2.2.1)
    (ZMod.val_injective _ he.2.2.2.1) (ZMod.val_injective _ he.2.2.2.2.1) (ZMod.val_injective _ he.2.2.2.2.2.1)
  subst F; rfl

open Groundwork Groundwork.PolyT
attribute [local fun_prop] Groundwork.PolyT.comp Groundwork.PolyT.const Groundwork.PolyT.fst Groundwork.PolyT.snd Groundwork.PolyT.prodMk P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219

private noncomputable def outw (q : curves) := encodeECFactorBlocks (groupBlock (G := curvePts q) (blockCount (bitLen q.1.val.val)))
private noncomputable def table (xs : List curves) (w : List Bool) : List Bool :=
  match xs with
  | [] => []
  | q::qs => if w = curveInput q then outw q else table qs w

private theorem table_poly (xs : List curves) : PolyT (table xs) := by
  induction xs with
  | nil => exact Groundwork.PolyT.const []
  | cons q qs ih => change PolyT fun w => if w = curveInput q then outw q else table qs w; fun_prop

private theorem table_good (q : curves) (xs : List curves) (h : q ∈ xs) : table xs (curveInput q) = outw q := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    by_cases e : q=x
    · subst x; simp [table]
    · simp [table,show curveInput q ≠ curveInput x from fun h => e (curve_inj h),ih (by simpa [e] using h)]

noncomputable def smallOut : List Bool → List Bool := by
  classical
  letI := Fintype.ofFinite curves
  exact table Finset.univ.toList

theorem smallOut_poly : PolyT smallOut := table_poly _
theorem smallOut_spec {p : ℕ} [Fact p.Prime] (hp : 3 < p) (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (hs : m89_ec_plan_ok (m := blockCount (bitLen p)) E none) :
    ∃ F : Fin (blockCount (bitLen p)) → List E.toAffine.Point,
      (∀ i, (F i).Nodup ∧ (F i).toFinset = m89_ec_plan_block E none i) ∧
      smallOut (encodeCurveInput p E) = encodeECFactorBlocks F := by
  classical
  letI := ecPointFintype E
  have bnd := ec_small_bound hp E hs
  let q : Pr := ⟨⟨p,by omega⟩,Fact.out⟩
  let c : curves := ⟨q,E⟩
  refine ⟨groupBlock (G := E.toAffine.Point) (blockCount (bitLen p)),fun i => ⟨Finset.nodup_toList _,Finset.toList_toFinset _⟩, ?_⟩
  letI := Fintype.ofFinite curves
  exact table_good c _ (Finset.mem_toList.mpr (Finset.mem_univ _))

theorem smallOut_bound : ∃ U : ℕ, ∀ w, (smallOut w).length ≤ U := by
  classical
  letI := Fintype.ofFinite curves
  let U := Finset.univ.sup (fun c => (outw c).length)
  refine ⟨U,fun w => ?_⟩
  have ht (xs : List curves) : (table xs w).length ≤ U := by
    induction xs with
    | nil => exact Nat.zero_le _
    | cons q qs ih => unfold table; split; exact Finset.le_sup (f:=fun c => (outw c).length) (Finset.mem_univ q); exact ih
  exact ht _
end DetDLP.ECEnumSmall

end

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace DetDLP.ECEnumStep
open M89S1 Groundwork Groundwork.PolyT
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
attribute [local fun_prop] Groundwork.PolyT.comp Groundwork.PolyT.const Groundwork.PolyT.fst Groundwork.PolyT.snd Groundwork.PolyT.prodMk
  Groundwork.PolyT.map Groundwork.PolyT.flatMap Groundwork.PolyT.filter Groundwork.PolyT.filterMap
  Groundwork.PolyT.mul Groundwork.PolyT.div Groundwork.PolyT.idxOf Groundwork.PolyT.length
  P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_id__1c5d0f44cc8f
  P2M_Groundwork_PolyT_cond__4c673073da15 P2M_Groundwork_PolyT_ite__226169acf219
  P2M_Groundwork_PolyT_some__e6a32bd6af45 ECEnumSmall.smallOut_poly

abbrev Word := List Bool
abbrev State := Bool × Bool × Word × List Word
def scan (s : State) (b : Bool) : State :=
  bif s.1 then bif s.2.1 then s else (false,true,b::s.2.2.1,s.2.2.2)
  else bif s.2.1 then bif b then (true,false,s.2.2.1,s.2.2.2) else (false,false,[],s.2.2.1.reverse :: s.2.2.2)
  else bif b then (false,true,[],s.2.2.2) else (true,true,[],s.2.2.2)
def fields (w : Word) := (w.foldl scan (false,false,[],[])).2.2.2.reverse

private theorem scan_size (s : State) (b : Bool) : len (scan s b) ≤ len s + 5 := by
  obtain ⟨i,j,w,l⟩ := s; cases i <;> cases j <;> cases b <;> simp [scan,len_pair,len_bools,len_bool,len_cons,len_nil] <;> omega
@[local fun_prop] theorem fields_poly : PolyT fields := by
  have h : PolyT (fun w : Word => w.foldl scan (false,false,[],[])) := by
    refine foldl_add (g:=fun _ => scan) (by fun_prop) (by fun_prop) (by unfold scan; fun_prop) ⟨_,PB.const 5,?_⟩
    exact fun _ s e _ => scan_size s e
  unfold fields; fun_prop

private theorem scan_frame (w acc : Word) (l : List Word) : (Encoding.frame w).foldl scan (false,true,acc,l) = (false,false,[],(acc.reverse++w)::l) := by
  induction w generalizing acc with
  | nil => simp [Encoding.frame,scan]
  | cons b w ih => change (Encoding.frame w).foldl scan (false,true,b::acc,l) = _; simpa using ih (b::acc)

@[simp] theorem fields_encode (l : List Word) : fields (Encoding.encodeList id l) = l := by
  have run (L a : List Word) : (Encoding.encodeList id L).foldl scan (false,false,[],a) = (true,true,[],L.reverse++a) := by
    induction L generalizing a with
    | nil => rfl
    | cons w L ih =>
      change (Encoding.frame w ++ Encoding.encodeList id L).foldl scan (false,true,[],a) = _
      rw [List.foldl_append,scan_frame]; simpa using ih (w::a)
  simp [fields,run]

private theorem frame_flat (w : Word) : Encoding.frame w = w.flatMap (fun b => [true,b]) ++ [false] := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa [Encoding.frame,List.flatMap] using congrArg (fun z => true::b::z) ih

@[local fun_prop] theorem enc_poly {α : Type} [Enc α] {g : α → List Word} (hg : PolyT g) : PolyT (fun x => Encoding.encodeList id (g x)) := by
  have he (l : List Word) : Encoding.encodeList id l = l.flatMap (fun u => true :: Encoding.frame u) ++ [false] := by
    induction l with
    | nil => rfl
    | cons w l ih => change true :: (Encoding.frame w ++ Encoding.encodeList id l) = _; simp [ih,List.flatMap,List.append_assoc]
  simp only [he,frame_flat]; fun_prop

abbrev W := List Bool
abbrev Cursor := W × W
def advance (c : Cursor) (_ : Bool) : Cursor :=
  bif c.2.headD false then (c.2.tail.headD false :: c.1,c.2.tail.tail) else c

def parse (w : W) := w.foldl advance ([],w.tail)
def first (w : W) := (parse w).1.reverse
def more (w : W) := (parse w).2.tail
private theorem parse_aux (x xs acc : W) : ∀ (fuel : W), x.length ≤ fuel.length →
    fuel.foldl advance (acc,Encoding.frame x ++ xs) = (x.reverse ++ acc,false :: xs) := by
  induction x generalizing acc with
  | nil => intro fuel _; induction fuel <;> simp_all [Encoding.frame,advance,List.foldl]
  | cons b x ih => intro fuel hf; cases fuel with
    | nil => simp at hf
    | cons k fuel => simpa [Encoding.frame,advance,List.foldl,List.append_assoc] using ih (b::acc) fuel (by simpa using hf)

private theorem flen (x : W) : (Encoding.frame x).length = 2*x.length+1 := by
  induction x with
  | nil => rfl
  | cons b x ih => change (Encoding.frame x).length + 1 + 1 = 2*(x.length+1)+1; omega

theorem parse_poly : PolyT parse := by
  apply PolyT.foldl_add (l:=fun w : W => w) (a:=fun w => ([],w.tail)) (g:=fun _ c b => advance c b)
  · fun_prop
  · fun_prop
  · unfold advance; fun_prop
  · refine ⟨fun _ => 3,PB.const 3,?_⟩
    intro w c b _; rcases c with ⟨x,y⟩; unfold advance; dsimp only [Prod.fst,Prod.snd]; cases h : y.headD false <;> simp [len_pair,len_bools] <;> omega

@[local fun_prop] theorem first_poly {α : Type} [Enc α] {f : α → W} (hf : PolyT f) : PolyT (fun x => first (f x)) :=
  PolyT.reverse (PolyT.fst (PolyT.comp parse_poly hf))
@[local fun_prop] theorem more_poly {α : Type} [Enc α] {f : α → W} (hf : PolyT f) : PolyT (fun x => more (f x)) :=
  PolyT.tail (PolyT.snd (PolyT.comp parse_poly hf))

def second (w : W) := first (more w)
def third (w : W) := second (more w)
def frame (w : W) := w.flatMap (fun b => [true,b]) ++ [false]
@[simp] theorem frame_correct (w : W) : frame w = Encoding.frame w := by induction w <;> simp_all [frame,Encoding.frame,List.foldr]
@[local fun_prop] theorem frame_poly {α : Type} [Enc α] {f : α → W} (hf : PolyT f) : PolyT (fun x => frame (f x)) := by
  unfold frame; apply PolyT.append; apply PolyT.flatMap (f:=fun _ b => [true,b]); fun_prop; exact hf; fun_prop



def pair (w v : W) := frame w ++ v
@[simp] theorem first_pair (w v : W) : first (true :: pair w v) = w := by
  simp only [first,parse,pair,frame_correct,List.tail_cons]; rw [parse_aux]; simp; simp [flen]; omega
@[simp] theorem more_pair (w v : W) : more (true :: pair w v) = v := by
  simp only [more,parse,pair,frame_correct,List.tail_cons]; rw [parse_aux]; rfl; simp [flen]; omega
abbrev enc := Encoding.encodeList (α := W) id
def atW (w : W) (n : ℕ) := (fields w).getD n []
@[local fun_prop] theorem atW_poly {α : Type} [Enc α] {x : α → W} {n : α → ℕ} (hx : PolyT x) (hn : PolyT n) : PolyT fun a => atW (x a) (n a) := by unfold atW; fun_prop
@[simp] theorem atW_enc (ws : List W) (n : ℕ) : atW (enc ws) n = ws.getD n [] := by simp [atW,enc]

def base (arg : W) := atW arg 0
def plan (arg : W) := atW arg 1
def threshold (arg : W) := atW (plan arg).tail 0
def seed (arg : W) := atW (plan arg).tail 1
def width (arg : W) := (bval (atW (base arg) 0) - 1).bits.length
def blocks (arg : W) := (seed arg).length / (4*width arg)
def q (arg : W) (i : ℕ) (w : W) := queryWord 4 (base arg) [threshold arg,seed arg,countWord i,w]
def point (b : ℕ) (w : W) := enc [countWord (w.headD false).toNat,countWord (bval (w.tail.take b).reverse),countWord (bval (w.tail.drop b).reverse)]

def st (a : W) (i : ℕ) (jobs pts rows : List W) := false :: enc [a,countWord i,enc jobs,enc pts,enc rows]
def ask (a : W) (i : ℕ) (w : W) (ws pts rows : List W) := false :: pair (st a i (w::ws) pts rows) (q a i w)
def dispatch (a : W) (i : ℕ) (ws pts rows : List W) :=
  if ws.isEmpty then
    let done := enc pts.reverse :: rows
    if i+1 < blocks a then ask a (i+1) [] [] [] done else true :: enc done.reverse
  else ask a i (ws.headD []) ws.tail pts rows

def process (a : W) (i : ℕ) (jobs pts rows : List W) (pos : Bool) :=
  let w := jobs.headD []; let ws := jobs.tail
  if pos then
    if w.length = 2*width a + 1 then dispatch a i ws (point (width a) w :: pts) rows
    else dispatch a i ((w++[false]) :: (w++[true]) :: ws) pts rows
  else dispatch a i ws pts rows

noncomputable def start (a : W) := if (plan a).headD false then ask a 0 [] [] [] [] else true :: ECEnumSmall.smallOut (base a)
noncomputable def ctrl (state ans : W) :=
  if state.headD false then start state else
    let v := state.tail
    process (atW v 0) (bval (atW v 1)) (fields (atW v 2)) (fields (atW v 3)) (fields (atW v 4)) (ans != encodeNatListBin [0])

noncomputable def step (w : W) := ctrl (first (true :: w)) (more (true :: w))

@[local fun_prop] theorem bp {α : Type} [Enc α] {a : α → W} (ha : PolyT a) : PolyT fun x => width (a x) := by unfold width base; fun_prop
@[local fun_prop] theorem blocks_poly {α : Type} [Enc α] {a : α → W} (ha : PolyT a) : PolyT fun x => blocks (a x) := by unfold blocks seed plan; fun_prop
@[local fun_prop] theorem pt_poly {α : Type} [Enc α] {b : α → ℕ} {w : α → W} (hb : PolyT b) (hw : PolyT w) : PolyT fun x => point (b x) (w x) := by unfold point countWord; fun_prop
@[local fun_prop] theorem ask_poly {α : Type} [Enc α] {a w : α → W} {i : α → ℕ} {ws ps rs : α → List W} (ha : PolyT a) (hw : PolyT w) (hi : PolyT i) (hs : PolyT ws) (hp : PolyT ps) (hr : PolyT rs) : PolyT fun x => ask (a x) (i x) (w x) (ws x) (ps x) (rs x) := by
  unfold ask pair st q queryWord base threshold seed plan countWord; fun_prop
@[local fun_prop] theorem disp_poly {α : Type} [Enc α] {a : α → W} {i : α → ℕ} {ws ps rs : α → List W} (ha : PolyT a) (hi : PolyT i) (hs : PolyT ws) (hp : PolyT ps) (hr : PolyT rs) : PolyT fun x => dispatch (a x) (i x) (ws x) (ps x) (rs x) := by unfold dispatch; fun_prop
@[local fun_prop] theorem proc_poly {α : Type} [Enc α] {a : α → W} {i : α → ℕ} {ws ps rs : α → List W} {pos : α → Bool} (ha : PolyT a) (hi : PolyT i) (hs : PolyT ws) (hp : PolyT ps) (hr : PolyT rs) (hpos : PolyT pos) : PolyT fun x => process (a x) (i x) (ws x) (ps x) (rs x) (pos x) := by unfold process; fun_prop
@[local fun_prop] theorem start_poly : PolyT start := by unfold start plan base; fun_prop

theorem step_poly : PolyT step := by unfold step ctrl; fun_prop

@[simp] theorem step_pair (v ans : W) : step (pair v ans) = ctrl v ans := by simp [step]
@[simp] theorem read_count (n : ℕ) : bval (countWord n) = n := by by_cases h : n = 0; subst n; rfl; simp [countWord,h,bval_bits]
@[simp] theorem ctrl_st (a ans : W) (i : ℕ) (ws ps rs : List W) : ctrl (st a i ws ps rs) ans = process a i ws ps rs (ans != encodeNatListBin [0]) := by simp [ctrl,st,enc,atW,fields_encode]

end DetDLP.ECEnumStep

end

section

set_option autoImplicit false
namespace DetDLP.ECEnumTrace
open M89S1 ECEnumStep Groundwork.PolyT
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
abbrev Job := ECEnumTrie.Job
abbrev names (jobs : List Job) := jobs.map Prod.snd

def arg {p m : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (L : Option (ℕ × ECSeed p m)) := enc [encodeCurveInput p E,m89_ec_plan_word L]

private theorem fields_map {α : Type} (f : α → W) (xs : List α) : fields (Encoding.encodeList f xs) = xs.map f := by
  have h : Encoding.encodeList f xs = enc (xs.map f) := by
    induction xs with
    | nil => rfl
    | cons x t ih => change true :: (_ ++ Encoding.encodeList f t) = true :: (_ ++ enc (t.map f)); rw [ih]; rfl
  rw [h,fields_encode]

variable {p : ℕ} [Fact p.Prime] {E : WeierstrassCurve (ZMod p)} {T : ℕ} {S : ECSeed p (blockCount (bitLen p))}

@[simp] theorem base_arg {m : ℕ} (L : Option (ℕ × ECSeed p m)) : base (arg E L) = encodeCurveInput p E := by simp [base,arg]
@[simp] theorem plan_arg {m : ℕ} (L : Option (ℕ × ECSeed p m)) : plan (arg E L) = m89_ec_plan_word L := by simp [plan,arg]
@[simp] theorem threshold_arg : threshold (arg E (some (T,S))) = countWord T := by simp [threshold,m89_ec_plan_word,atW]
@[simp] theorem seed_arg : seed (arg E (some (T,S))) = List.ofFn (ecBits S) := by simp [seed,m89_ec_plan_word,atW]
@[simp] theorem width_arg {m : ℕ} (L : Option (ℕ × ECSeed p m)) : width (arg E L) = bitLen p := by
  simp only [width,base_arg,atW,encodeCurveInput,encodeNatListBin,fields_map,List.map_cons,List.getD_cons_zero,read_count]
  rw [Nat.size_eq_bits_len]
  apply le_antisymm
  · apply Nat.size_le.2; have h : p ≤ 2^(bitLen p) := Nat.le_pow_clog (by decide) _; have hp := (Fact.out : Nat.Prime p).two_le; omega
  · apply (Nat.clog_le_iff_le_pow (by decide : 1<2)).2; have h := Nat.size_le.mp (le_refl (p-1).size); omega
@[simp] theorem blocks_arg : blocks (arg E (some (T,S))) = blockCount (bitLen p) := by
  simp only [blocks,seed_arg,width_arg,List.length_ofFn]
  change blockCount (bitLen p)*4*bitLen p/(4*bitLen p) = _
  rw [Nat.mul_assoc]; apply Nat.mul_div_cancel; exact Nat.mul_pos (by decide) (Nat.clog_pos (by decide) (Fact.out : Nat.Prime p).two_le)

private theorem fromLE_eq (w : W) : ECEnumDigits.fromLE w = bval w := by
  induction w with
  | nil => rfl
  | cons x w ih => rw [ECEnumDigits.fromLE,bval_cons,ih,Nat.add_comm]

@[simp] theorem point_correct (P : E.toAffine.Point) : point (bitLen p) (ECEnumSemantic.code P) = encodeNatListBin (pointCoords P) := by
  rw [←ECEnumSemantic.coords_code P]; simp [point,ECEnumSemantic.coords,encodeNatListBin,enc,Encoding.encodeList,fromLE_eq]

@[simp] theorem ans_pos (n : ℕ) : (encodeNatListBin [n] != encodeNatListBin [0]) = decide (n ≠ 0) := by
  by_cases hn : n = 0
  · subst n; simp
  · have h : encodeNatListBin [n] ≠ encodeNatListBin [0] := by
      intro h; have g := congrArg (fun w => bval (atW w 0)) h
      simpa [atW,encodeNatListBin,fields_map,hn] using g
    simp [h,hn]

/-- A transcript from a controller emission through its final output. Keep the peak word size and query count explicit. -/
inductive Trace (V : W → W → Prop) (B : ℕ) (out : W) : ℕ → W → Prop where
  | stop (hlen : out.length ≤ B) : Trace V B out 0 (true :: out)
  | ask {s q ans n} (legal : V q ans) (hsq : (pair s q).length ≤ B) (hsa : (pair s ans).length ≤ B) (ha : ans.length ≤ B)
      (next : Trace V B out n (step (pair s ans))) : Trace V B out (n+1) (false :: pair s q)

def Rounds (O : PrimitiveMachine) (o : Fin O.tapeCount) (time space : ℝ) :=
  Nat.rec (motive := fun _ => W → W → W → ℕ → Prop)
    (fun _ _ _ _ => False)
    (fun _ prev s a z B =>
      (step (pair s a) = true :: z ∧ (pair s a).length ≤ B ∧ z.length ≤ B) ∨
      ∃ s' q ans, step (pair s a) = false :: pair s' q ∧ (pair s a).length ≤ B ∧
        (pair s' q).length ≤ B ∧ ans.length ≤ B ∧ RunsWithin O o q ans time space ∧ prev s' ans z B)

theorem to_rounds {V : W → W → Prop} {B n : ℕ} {s a z : W} (O : PrimitiveMachine) (o : Fin O.tapeCount) (t u : ℝ)
    (oracle : ∀ q ans, V q ans → RunsWithin O o q ans t u)
    (h : Trace V B z n (step (pair s a))) (hlen : (pair s a).length ≤ B) : Rounds O o t u (n+1) s a z B := by
  generalize he : step (pair s a) = word at h
  induction h generalizing s a with
  | stop hz => exact Or.inl ⟨he,hlen,hz⟩
  | ask legal hsq hsa ha next ih => exact Or.inr ⟨_,_,_,he,hlen,hsq,ha,oracle _ _ legal,ih hsa rfl⟩

def Good (N : ℕ) (jobs : List Job) := ∀ j ∈ jobs, j.1 + j.2.length = N
abbrev visit (cnt : W → ℕ) (jobs : List Job) := jobs.flatMap fun j => ECEnumTrie.enumerate cnt j.1 j.2
abbrev cost (cnt : W → ℕ) (jobs : List Job) := (jobs.map fun j => ECEnumTrie.calls cnt j.1 j.2).sum

theorem walk {a : W} {i N B k P : ℕ} {z : W} {V : W → W → Prop} {cnt : W → ℕ} {rows : List W}
    (hN : N = 2*width a + 1)
    (legal : ∀ w : W, w.length ≤ N → V (q a i w) (encodeNatListBin [cnt w]))
    (jobs : List Job) (pts : List W) (good : Good N jobs)
    (pmax : ∀ w : W, w.length = N → (point (width a) w).length ≤ P)
    (pg : ∀ u ∈ pts, u.length ≤ P)
    (bound : ∀ (js : List Job) (w : W) (ps : List W), Good N js → js ≠ [] → (names js).headD [] = w → (∀ u ∈ ps, u.length ≤ P) →
      ps.length + cost cnt js ≤ pts.length + cost cnt jobs →
      let state := st a i (names js) ps rows
      (pair state (q a i w)).length ≤ B ∧ (pair state (encodeNatListBin [cnt w])).length ≤ B ∧ (encodeNatListBin [cnt w]).length ≤ B)
    (doneTrace : Trace V B z k (dispatch a i [] (((visit cnt jobs).map (point (width a))).reverse ++ pts) rows)) :
    Trace V B z (k+cost cnt jobs) (dispatch a i (names jobs) pts rows) := by
  generalize hk : cost cnt jobs = fuel
  induction fuel using Nat.strong_induction_on generalizing jobs pts with
  | h fuel ih =>
    cases jobs with
    | nil => simpa [cost] using (hk ▸ doneTrace : Trace _ _ _ _ _)
    | cons j js =>
      obtain ⟨n,w⟩ := j
      have hn := good (n,w) (by simp)
      have gs : Good N js := fun j hj => good j (by simp [hj])
      have bs := bound ((n,w)::js) w pts good (by simp) rfl pg (by omega)
      let s := st a i (w::names js) pts rows
      have e (next : List Job) (ps : List W) (hg : Good N next) (hpg : ∀ u ∈ ps, u.length ≤ P) (hf : cost cnt next + 1 = fuel)
          (hd : ps.length + cost cnt next ≤ pts.length + fuel)
          (hpts : ((visit cnt next).map (point (width a))).reverse ++ ps = ((visit cnt ((n,w)::js)).map (point (width a))).reverse ++ pts)
          (hstep : process a i (w::names js) pts rows (decide (cnt w ≠ 0)) = dispatch a i (names next) ps rows) :
          Trace V B z (k+fuel) (dispatch a i (names ((n,w)::js)) pts rows) := by
        have hrec := ih (cost cnt next) (by omega) next ps hg hpg (fun ns u v a1 a2 a3 a4 le => bound ns u v a1 a2 a3 a4 (by omega)) (by rw [hpts]; exact doneTrace) rfl
        have ht : Trace V B z (k+cost cnt next) (step (pair s (encodeNatListBin [cnt w]))) := by simpa only [s,step_pair,ctrl_st,ans_pos,hstep] using hrec
        rw [←hf,Nat.add_succ]
        exact Trace.ask (legal w (by dsimp at hn; omega)) bs.1 bs.2.1 bs.2.2 ht
      by_cases hz : cnt w = 0
      · apply e js pts gs pg
        · cases n <;> simp [cost,ECEnumTrie.calls,hz] at hk ⊢ <;> omega
        · cases n <;> simp [cost,ECEnumTrie.calls,hz] at hk ⊢ <;> omega
        · cases n <;> simp [visit,ECEnumTrie.enumerate,hz]
        · simp [process,hz]
      · cases n with
        | zero =>
          apply e js (point (width a) w::pts) gs
          · intro u hu; rcases List.mem_cons.mp hu with rfl | hu; exact pmax _ (by simpa using hn); exact pg _ hu
          · simp [cost,ECEnumTrie.calls] at hk ⊢; omega
          · simp [cost,ECEnumTrie.calls] at hk ⊢; omega
          · simp [visit,ECEnumTrie.enumerate,hz,List.append_assoc]
          · simp [process,hz,show w.length = 2*width a+1 by simpa [hN] using hn]
        | succ n =>
          let next : List Job := (n,w++[false]) :: (n,w++[true]) :: js
          apply e next pts
          · intro j hj; simp only [next,List.mem_cons] at hj; rcases hj with rfl | rfl | hj <;> first | exact gs _ hj | simp at hn ⊢; omega
          · exact pg
          · simp [cost,next,ECEnumTrie.calls,hz] at hk ⊢; omega
          · simp [cost,next,ECEnumTrie.calls,hz] at hk ⊢; omega
          · simp [visit,next,ECEnumTrie.enumerate,hz,List.append_assoc]
          · simp [process,hz,next,names,show w.length ≠ 2*width a+1 by dsimp at hn; omega]

end DetDLP.ECEnumTrace

end

section
set_option autoImplicit false
namespace DetDLP.ECEnumBounds
open ECEnumTrace ECEnumStep Groundwork.PolyT M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem frame_len (w : W) : (Encoding.frame w).length = 2*w.length+1 := by
  induction w with | nil => rfl | cons _ w ih => change (Encoding.frame w).length+1+1 = 2*(w.length+1)+1; omega
@[simp] theorem pair_len (x y : W) : (pair x y).length = 2*x.length+1+y.length := by simp [pair,frame_len]
@[simp] theorem enc_nil : (enc []).length = 1 := rfl
@[simp] theorem enc_cons (x : W) (xs : List W) : (enc (x::xs)).length = 2*x.length+2+(enc xs).length := by
  change (true :: (Encoding.frame x ++ enc xs)).length = _; simp [frame_len]; omega

theorem enc_le (xs : List W) (H : ℕ) (h : ∀ w ∈ xs, w.length ≤ H) : (enc xs).length ≤ (2*H+2)*xs.length+1 := by
  induction xs with
  | nil => simp
  | cons w ws ih => have := ih (fun u hu => h u (List.mem_cons_of_mem _ hu)); have := h w (by simp); simp [Nat.mul_succ]; omega

theorem cwlen (n : ℕ) : (countWord n).length ≤ n.size+1 := by by_cases e : n = 0 <;> simp [countWord,e,Nat.size_eq_bits_len]
theorem cwnat (n : ℕ) : (countWord n).length ≤ n+1 := (cwlen n).trans (by have := Nat.size_le.mpr (Nat.lt_two_pow_self (n:=n)); omega)
theorem cwb (v : W) : (countWord (bval v)).length ≤ v.length+1 := (cwlen _).trans (by have := Nat.size_le.mpr (bval_lt v); omega)

theorem point_len (b : ℕ) (w : W) : (point b w).length ≤ 20*(w.length+1) := by
  have h := cwb ((w.tail.take b).reverse); have h' := cwb ((w.tail.drop b).reverse)
  have hb := cwnat (w.headD false).toNat; have hbit : (w.headD false).toNat ≤ 1 := by cases w.headD false <;> decide
  simp only [point,enc_cons,enc_nil,List.length_reverse,List.length_take,List.length_drop,List.length_tail] at *; omega

theorem list_cost (c : W → ℕ) (js : List Job) : js.length ≤ cost c js := by
  induction js with
  | nil => rfl
  | cons j js ih => obtain ⟨n,w⟩ := j; cases n <;> by_cases e : c w = 0 <;> simp [cost,ECEnumTrie.calls,e] at * <;> omega

def big (H : ℕ) := 1000000 * H^6

theorem large_state {a w : W} {i N H : ℕ} {js : List Job} {ps rs : List W} {cnt : W → ℕ}
    (hH : 10 ≤ H) (ha : a.length ≤ H) (hb : (base a).length ≤ H) (ht : (threshold a).length ≤ H)
    (hs : (seed a).length ≤ H) (hi : i ≤ H) (hN : N ≤ H) (hg : Good N js)
    (hw : w.length ≤ N) (hc : cnt w ≤ H) (hnum : ps.length + cost cnt js ≤ 3*H^2)
    (hp : ∀ u ∈ ps, u.length ≤ 20*(N+1)) (hrl : rs.length ≤ H)
    (hr : ∀ r ∈ rs, r.length ≤ 100*H^2) :
    let state := st a i (names js) ps rs
    (pair state (q a i w)).length ≤ big H ∧
    (pair state (encodeNatListBin [cnt w])).length ≤ big H ∧ (encodeNatListBin [cnt w]).length ≤ big H := by
  intro state
  have hj := enc_le (names js) N (by intro v hv; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv; have := hg j hj; omega)
  have hps := enc_le ps (20*(N+1)) hp; have hrs := enc_le rs (100*H^2) hr
  have hl := list_cost cnt js; simp only [names,List.length_map] at hj
  have e1 : (enc (names js)).length ≤ (2*H+2)*(3*H^2)+1 := hj.trans (by gcongr <;> omega)
  have e2 : (enc ps).length ≤ (40*H+40+2)*(3*H^2)+1 := hps.trans (by gcongr <;> omega)
  have e3 : (enc rs).length ≤ (2*(100*H^2)+2)*H+1 := hrs.trans (by gcongr)
  have ic := cwnat i; have cc := cwnat (cnt w)
  have qa : (q a i w).length ≤ 10*H+100 := by change (enc [countWord 4,base a,threshold a,seed a,countWord i,w]).length ≤ _; simp only [enc_cons,enc_nil]; have := cwnat 4; omega
  have an : (encodeNatListBin [cnt w]).length ≤ 2*H+5 := by change (enc [countWord (cnt w)]).length ≤ _; simp; omega
  have hmon (d : ℕ) (hd : d ≤ 6) : H^d ≤ H^6 := Nat.pow_le_pow_right (by omega) hd
  have h0 := hmon 0 (by decide); have h1 := hmon 1 (by decide); have h2 := hmon 2 (by decide); have h3 := hmon 3 (by decide)
  simp only [pow_zero,pow_one] at h0 h1
  simp only [state,st,List.length_cons,enc_cons,enc_nil,pair_len,big]
  refine ⟨?_,?_,?_⟩ <;> nlinarith only [h0,h1,h2,h3,e1,e2,e3,ha,ic,hi,qa,an]

end DetDLP.ECEnumBounds

end

section
set_option autoImplicit false
namespace DetDLP.ECEnumRows
open ECEnumTrace ECEnumStep ECEnumBounds M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

variable {p : ℕ} [Fact p.Prime] {E : WeierstrassCurve (ZMod p)} {T : ℕ} {S : ECSeed p (blockCount (bitLen p))}
abbrev valid (b : ℕ) (q ans : W) := ∃ n, Query q b n ∧ ans = encodeNatListBin [n]

theorem root_words (D : Finset E.toAffine.Point) :
    let cnt := elemCount D ECEnumSemantic.code
    let N := 2*bitLen p+1
    ∃ F : List E.toAffine.Point, F.Nodup ∧ F.toFinset = D ∧
      F.map ECEnumSemantic.code = ECEnumTrie.enumerate cnt N [] := by
  obtain ⟨F,hf,hd,hw⟩ := ECEnumSemantic.encoded_block D
  refine ⟨F,hf,hd,hw.trans ?_⟩
  apply Eq.trans (ECEnumTrie.execute_spec _ _ _ ?_).2
  · simp [ECEnumTrie.result]
  · simp only [ECEnumTrie.budget,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
    rw [ECEnumSemantic.count_eq]; simpa using ECEnumTrie.root_calls (D.toList.map ECEnumSemantic.code) (2*bitLen p+1) (by intro w hw; obtain ⟨P,_,rfl⟩ := List.mem_map.mp hw; exact ECEnumSemantic.code_len P)

theorem enc_map {α : Type} (f : α → W) (l : List α) : enc (l.map f) = Encoding.encodeList f l := by
  induction l with | nil => rfl | cons x l ih => change true :: (_ ++ enc (l.map f)) = true :: (_ ++ Encoding.encodeList f l); rw [ih]; rfl

noncomputable abbrev D (E : WeierstrassCurve (ZMod p)) (T : ℕ) (S : ECSeed p (blockCount (bitLen p))) := ecFactorBlock E T S
noncomputable def size (E : WeierstrassCurve (ZMod p)) (T : ℕ) (S : ECSeed p (blockCount (bitLen p))) := ∑ i, (D E T S i).card

theorem traces (hp : 3 < p) [E.IsElliptic] (hok : m89_ec_plan_ok E (some (T,S))) (H : ℕ)
    (hH : 10 ≤ H) (ha : (arg E (some (T,S))).length ≤ H) (hb : (encodeCurveInput p E).length ≤ H)
    (ht : (countWord T).length ≤ H) (hs : (List.ofFn (ecBits S)).length ≤ H)
    (hN : 2*bitLen p+1 ≤ H) (hm : blockCount (bitLen p) ≤ H) (hD : size E T S ≤ H) :
    ∃ (F : Fin (blockCount (bitLen p)) → List E.toAffine.Point) (n : ℕ),
      (∀ i, (F i).Nodup ∧ (F i).toFinset = D E T S i) ∧ n ≤ 3*H^3 ∧
      Trace (valid (bitLen p)) (big H) (encodeECFactorBlocks F) n (step (pair (arg E (some (T,S))) [])) := by
  classical
  let a := arg E (some (T,S)); let m := blockCount (bitLen p); let N := 2*bitLen p+1
  let cnt (i : Fin m) := elemCount (D E T S i) ECEnumSemantic.code
  choose F hf hd he using fun i : Fin m => root_words (D E T S i)
  let row (i : Fin m) := Encoding.encodeList (fun x : E.toAffine.Point => encodeNatListBin (pointCoords x)) (F i)
  let rows := List.ofFn row
  let out := encodeECFactorBlocks F
  have hout : out = enc rows := by unfold out encodeECFactorBlocks rows; rw [←enc_map,List.map_ofFn]; rfl
  have card (i : Fin m) : (D E T S i).card ≤ H := (Finset.single_le_sum (f := fun i => (D E T S i).card) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hD
  have fl (i : Fin m) : (F i).length ≤ H := by rw [←List.toFinset_card_of_nodup (hf i),hd]; exact card i
  have roweq (i : Fin m) : enc ((ECEnumTrie.enumerate (cnt i) N []).map (point (width a))) = row i := by
    rw [←he,List.map_map,enc_map]; simp [a,row,Function.comp_def]
  have rowlen (i : Fin m) : (row i).length ≤ 100*H^2 := by
    rw [←roweq]; refine (enc_le _ (20*(N+1)) ?_).trans ?_
    · intro w hw; obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw; have len := ECEnumTrie.length_of_mem _ _ _ _ hv; simpa [len] using point_len (width a) v
    · rw [←he]; simp only [List.length_map]; have q := Nat.mul_le_mul (show 2*(20*(N+1))+2 ≤ 50*H by omega) (fl i); nlinarith [Nat.one_le_pow 2 H (by omega)]
  have rlen (r : W) (hr : r ∈ rows) : r.length ≤ 100*H^2 := by obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr; exact rowlen i
  have outlen : out.length ≤ big H := by
    rw [hout]; apply (enc_le _ _ rlen).trans; simp only [rows,List.length_ofFn]; have h := Nat.mul_le_mul_left (2*(100*H^2)+2) hm
    dsimp [big]; nlinarith only [h,Nat.pow_le_pow_right (by omega : 0 < H) (by decide : 3 ≤ 6),Nat.pow_le_pow_right (by omega : 0 < H) (by decide : 1 ≤ 6),Nat.one_le_pow 6 H (by omega)]
  have all (i : Fin m) : ∃ n, n ≤ (m-i.val)*(3*H^2) ∧ Trace (valid (bitLen p)) (big H) out n (ask a i.val [] [] [] (rows.take i.val).reverse) := by
    generalize hrem : m-i.val = rem
    induction rem using Nat.strong_induction_on generalizing i with
    | h rem ih =>
      have il := i.isLt
      let rs := (rows.take i.val).reverse
      have eq : enc ((ECEnumTrie.enumerate (cnt i) N []).map (point (width a))) :: rs = (rows.take (i.val+1)).reverse := by
        rw [roweq,List.take_add_one,(show rows[i.val]? = some (row i) by simp [rows])]; simp [rs]
      have finish : ∃ k, k ≤ (m-(i.val+1))*(3*H^2) ∧ Trace (valid (bitLen p)) (big H) out k (dispatch a i.val [] (((ECEnumTrie.enumerate (cnt i) N []).map (point (width a))).reverse) rs) := by
        by_cases hn : i.val+1 < m
        · obtain ⟨k,hle,ht⟩ := ih (m-(i.val+1)) (by omega) ⟨i.val+1,hn⟩ rfl
          refine ⟨k,hle,?_⟩; simp only [dispatch,List.isEmpty_nil,if_true,List.reverse_reverse,eq]; simpa [a,m,hn] using ht
        · refine ⟨0,by omega,?_⟩
          have hfull : rows.take (i.val+1) = rows := List.take_of_length_le (by simp [rows]; omega)
          simp only [dispatch,List.isEmpty_nil,if_true,List.reverse_reverse,eq,hfull]; simpa [a,m,hn,hout] using (Trace.stop (V:=valid (bitLen p)) outlen)
      obtain ⟨k,hk,hfinish⟩ := finish
      let jobs : List Job := [(N,[])]
      have hc : cost (cnt i) jobs ≤ 3*H^2 := by
        have z := ECEnumTrie.root_calls ((D E T S i).toList.map ECEnumSemantic.code) N (by intro w hw; obtain ⟨P,_,rfl⟩ := List.mem_map.mp hw; exact ECEnumSemantic.code_len P)
        simp only [List.length_map,Finset.length_toList] at z
        simp only [cnt,jobs,cost,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,ECEnumSemantic.count_eq]
        apply z.trans; have hh : N*(D E T S i).card ≤ H*H := Nat.mul_le_mul hN (card i); nlinarith [Nat.one_le_pow 2 H (by omega)]
      refine ⟨k+cost (cnt i) jobs,?_,?_⟩
      · rw [show rem=(m-(i.val+1))+1 by omega,Nat.succ_mul]; omega
      · apply walk (N:=N) (cnt:=cnt i) (P:=20*(N+1)) (by simp [a,N]) (jobs:=jobs) (pts:=[]) (rows:=rs)
        · intro w hw; exact ⟨cnt i w,by simpa [q,a] using ECEnumSemantic.ec_query hp hok i w hw,rfl⟩
        · simp [Good,jobs]
        · intro w hw; simpa [hw] using point_len (width a) w
        · simp
        · intro js w ps hg hj eh pg num
          have hw : w.length ≤ N := by cases js with | nil => contradiction | cons j t => have := hg j (by simp); change j.2 = w at eh; rw [←eh]; omega
          apply large_state (H:=H) (N:=N) hH ha (by simpa [a] using hb) (by simpa [a] using ht) (by simpa [a] using hs) (by omega) hN hg hw
          · exact (Finset.card_filter_le _ _).trans (card i)
          · simpa using num.trans (by simpa using hc)
          · exact pg
          · simp [rs]; omega
          · intro r hr; exact rlen r (List.mem_of_mem_take (List.mem_reverse.mp hr))
        · simpa [jobs,visit] using hfinish
  have hm0 : 0 < m := by have : 2 ≤ m := le_max_left ..; omega
  obtain ⟨n,hle,tr⟩ := all ⟨0,hm0⟩
  refine ⟨F,n,fun i => ⟨hf i,hd i⟩,?_,?_⟩
  · simp at hle; nlinarith only [hle,Nat.mul_le_mul_right (3*H^2) hm]
  · have h1 : a.headD false = true := rfl
    have h2 : (plan a).headD false = true := by simp [a,m89_ec_plan_word]
    change Trace _ _ out n (step (pair a [])); simpa only [step_pair,ctrl,h1,if_true,start,h2,List.take_zero,List.reverse_nil,Fin.val_zero] using tr

end DetDLP.ECEnumRows

end

section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DetDLP.ECEnumGrowth
open ECEnumTrace ECEnumStep ECEnumBounds ECEnumRows M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
private theorem scale_ge_one {b : ℕ} (hb : 1 ≤ b) : 1 ≤ (b : ℝ) / (logSafe b)^((1:ℝ)/4) := by
  have hbr : (1:ℝ) ≤ b := by exact_mod_cast hb
  have hl : logSafe b ≤ (b:ℝ) := by
    apply max_le hbr
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) (by positivity)).mpr
    rw [Real.rpow_natCast]; apply max_le
    · exact_mod_cast (show 2 ≤ 2^b by exact le_trans (by decide : 2 ≤ 2^1) (Nat.pow_le_pow_right (by decide) hb))
    · exact_mod_cast (show b < 2^b from Nat.lt_two_pow_self).le
  have hg : 1 ≤ logSafe (b:ℝ) := le_max_left _ _
  have hp : (logSafe (b:ℝ))^((1:ℝ)/4) ≤ logSafe b := by
    simpa using Real.rpow_le_rpow_of_exponent_le hg (by norm_num : (1:ℝ)/4 ≤ 1)
  apply (one_le_div (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hg) _)).mpr
  exact hp.trans hl
theorem absorb_prod (K k n b : ℕ) (hb : 1 ≤ b) : (K:ℝ) * (mainSpaceBound k b)^n ≤ mainSpaceBound (K+n*k) b := by
  let s := (b:ℝ)/(logSafe b)^((1:ℝ)/4)
  have hs : 1 ≤ s := scale_ge_one hb
  have W (i : ℕ) : mainSpaceBound i b = (2:ℝ)^((i:ℝ)*s) := by unfold mainSpaceBound s; congr 1; ring
  rw [W,W,← Real.rpow_mul_natCast (by norm_num)]
  have hK : (K:ℝ) ≤ (2:ℝ)^((K:ℝ)*s) := by
    calc (K:ℝ) ≤ (2:ℝ)^(K:ℝ) := by rw [Real.rpow_natCast]; exact_mod_cast (Nat.lt_two_pow_self (n:=K)).le
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [Nat.cast_nonneg (α:=ℝ) K])
  calc _ ≤ (2:ℝ)^((K:ℝ)*s) * (2:ℝ)^((k:ℝ)*s*(n:ℕ)) := mul_le_mul_of_nonneg_right hK (by positivity)
       _ = _ := by rw [←Real.rpow_add (by norm_num)]; push_cast; congr 1; ring


private theorem blocks_le (b : ℕ) : blockCount b ≤ b+2 := by
  apply max_le (by omega) (Nat.ceil_le.mpr ?_)
  have u : Nat.clog 2 (b+2) ≤ b+2 := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 (Nat.lt_pow_self (by decide)).le
  have v : 1 ≤ Nat.clog 2 (b+2) := Nat.clog_pos (by decide) (by omega)
  exact (Real.rpow_le_self_of_one_le (by exact_mod_cast v) (by norm_num)).trans (by exact_mod_cast u)

variable {p : ℕ} [Fact p.Prime] {E : WeierstrassCurve (ZMod p)}

private theorem fieldcw (n : ℕ) (hn : n ≤ p) : (countWord n).length ≤ bitLen p + 2 := by
  apply (cwlen _).trans; have eq : n.size ≤ bitLen p + 1 := by
    apply Nat.size_le.2; rw [pow_succ]; have h : p ≤ 2^(bitLen p) := Nat.le_pow_clog (by decide) _; have : 0 < 2^(bitLen p) := by positivity
    omega
  omega

theorem curve_len : (encodeCurveInput p E).length ≤ 12*(bitLen p+2)+13 := by
  change (enc [countWord p,countWord E.a₁.val,countWord E.a₂.val,countWord E.a₃.val,countWord E.a₄.val,countWord E.a₆.val]).length ≤ _
  simp only [enc_cons,enc_nil]; have h := fieldcw p le_rfl; have h1 := fieldcw E.a₁.val E.a₁.val_lt.le; have h2 := fieldcw E.a₂.val E.a₂.val_lt.le; have h3 := fieldcw E.a₃.val E.a₃.val_lt.le; have h4 := fieldcw E.a₄.val E.a₄.val_lt.le; have h6 := fieldcw E.a₆.val E.a₆.val_lt.le; omega

def polybase (b : ℕ) := 1000*(b+2)^2

theorem lengths {T : ℕ} {S : ECSeed p (blockCount (bitLen p))} (hok : m89_ec_plan_ok E (some (T,S))) :
    let base := polybase (bitLen p)
    (arg E (some (T,S))).length ≤ base ∧ (encodeCurveInput p E).length ≤ base ∧
    (countWord T).length ≤ base ∧ (List.ofFn (ecBits S)).length ≤ base ∧ 2*bitLen p+1 ≤ base ∧ blockCount (bitLen p) ≤ base ∧ 10 ≤ base := by
  obtain ⟨h64,h4096,hT,_⟩ := hok
  have hfield := fieldcw T (hT ▸ ECEnumSemantic.threshold_le p _ _ (le_max_left ..) h64 h4096)
  have hcv := curve_len (E:=E)
  let b := bitLen p; let m := blockCount b
  have hblocks := blocks_le b
  have sd : (List.ofFn (ecBits S)).length = m*4*b := List.length_ofFn
  have hs := Nat.mul_le_mul_right (4*b) hblocks
  dsimp only; change (enc [encodeCurveInput p E,true :: enc [countWord T,List.ofFn (ecBits S)]]).length ≤ _ ∧ _
  simp only [enc_cons,enc_nil,List.length_cons,sd,polybase]; change (countWord T).length ≤ b+2 at hfield; change (encodeCurveInput p E).length ≤ 12*(b+2)+13 at hcv
  dsimp [m,b] at *; refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> nlinarith only [hfield,hcv,hs,hblocks,Nat.zero_le b]

theorem small_length : (arg E (none : Option (ℕ × ECSeed p (blockCount (bitLen p))))).length ≤ polybase (bitLen p) := by
  change (enc [encodeCurveInput p E,[false]]).length ≤ _; simp only [enc_cons,enc_nil,List.length_cons,List.length_nil,polybase]; nlinarith [curve_len (E:=E)]

theorem size_bound : ∃ C : ℕ, ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (T : ℕ) (S : ECSeed p (blockCount (bitLen p))), m89_ec_plan_ok E (some (T,S)) → (ECEnumRows.size E T S : ℝ) ≤ mainSpaceBound C (bitLen p) := by
  obtain ⟨C,hC⟩ := stage1_complexity_dominance.2.2.1 1 32772
  refine ⟨C,?_⟩; intro p inst hp E el T S hok
  letI := ecPointFintype E; let g := Fintype.card E.toAffine.Point; let m := blockCount (bitLen p)
  let F : Fin m → List E.toAffine.Point := fun i => (ecFactorBlock E T S i).toList
  have hs := hasse_ec_point_count_bound p hp E
  change |(g:ℝ) - ((p:ℝ)+1)| ≤ 2*Real.sqrt p at hs
  have hg : g ≤ 3*p := by
    have h := (abs_le.mp hs).2; have hh : (3:ℝ) < p := by exact_mod_cast hp
    have sq := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) p)
    have z : (g:ℝ) ≤ 3*(p:ℝ) := by nlinarith only [h,hh,sq,sq_nonneg (Real.sqrt (p:ℝ)-1)]
    exact_mod_cast z
  obtain ⟨h64,h4096,eq,_⟩ := hok
  have h := stage1_cond_exp_derand_and_size_bounds.2.2.2.2 p m E F hp (le_max_left ..) (fun i => Finset.nodup_toList _) hs (Or.inr ⟨h64,h4096,S,fun i => by simp [F,eq,m]⟩)
  have dom := (hC p g (by omega) hg).2
  let c := (32772:ℝ)*((m:ℝ)^2+(m:ℝ)*(g:ℝ)^((1:ℝ)/(m:ℝ)))
  change polyBound 1 (bitLen p)*c ≤ _ at dom
  apply le_trans _ dom
  have h' : (ECEnumRows.size E T S:ℝ) ≤ c := by simpa [F,ECEnumRows.size,D,c,m,g] using h
  have pos : 0 ≤ c := by dsimp [c]; positivity
  unfold polyBound; simp; nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) (bitLen p)) pos]

noncomputable def planSize (E : WeierstrassCurve (ZMod p)) : Option (ℕ × ECSeed p (blockCount (bitLen p))) → ℕ
  | none => 0
  | some (t,s) => ECEnumRows.size E t s

/-- Uniform absorption for the oracle loop, including the word lengths and total number of calls. -/
theorem resources (U I J : ℕ) : ∃ K : ℕ, ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (L : Option (ℕ × ECSeed p (blockCount (bitLen p)))), m89_ec_plan_ok E L →
    let sz := planSize E L
    let b := bitLen p; let H := polybase b + sz + U + 10
    let τ := mainSpaceBound J b; let σ := polyBound J b
    ((3*H^3+1:ℕ):ℝ)*(polyBound I (big H)+(I:ℝ)*(τ+σ+1)) ≤ mainSpaceBound K b ∧
    polyBound I (big H)+(I:ℝ)*(σ+1) ≤ mainSpaceBound K b := by
  obtain ⟨Cs,hCs⟩ := size_bound
  obtain ⟨Cp,hCp⟩ := stage1_complexity_dominance.2.2.1 2 0
  obtain ⟨Cj,hCj⟩ := stage1_complexity_dominance.2.2.1 J 0
  let C := max (max Cs Cp) (max J Cj)
  let A := 5000+U+12
  let D := A+1*C
  let G := 1000001+6*D
  let P := I+I*G
  let Z := max P (max C D)
  refine ⟨(4*(1+3*I))+4*Z,?_⟩
  intro p inst hp E el L ok sz b H τ σ
  have hb : 1 ≤ b := Nat.clog_pos (by decide) (by omega : 1 < p)
  have mono (a k : ℕ) (h : a ≤ k) := (stage1_complexity_dominance.1 a k b h).1
  have hCpos (k : ℕ) : 1 ≤ mainSpaceBound k b := by unfold mainSpaceBound; apply Real.one_le_rpow (by norm_num); have hl : 0 < logSafe (b:ℝ) := lt_of_lt_of_le zero_lt_one (le_max_left ..); positivity
  have s0 : (sz:ℝ) ≤ mainSpaceBound C b := by
    dsimp only [sz]; clear_value sz
    cases L with
    | none => simpa only [planSize,Nat.cast_zero] using (show (0:ℝ) ≤ 1 by norm_num).trans (hCpos C)
    | some v => obtain ⟨t,s⟩ := v; exact (hCs p hp E t s ok).trans (mono Cs C ((le_max_left Cs Cp).trans (le_max_left (max Cs Cp) (max J Cj))))
  have poly := ((hCp p 0 (by omega) (by omega)).1).trans (mono Cp C ((le_max_right Cs Cp).trans (le_max_left (max Cs Cp) (max J Cj))))
  change (2:ℝ)*((b:ℝ)+1)^2 ≤ mainSpaceBound C b at poly
  have hH : (H:ℝ) ≤ mainSpaceBound D b := by
    apply le_trans _ (by simpa only [pow_one] using absorb_prod A C 1 b hb)
    dsimp [H,polybase,A]; push_cast
    nlinarith only [poly,s0,hCpos C,mul_le_mul_of_nonneg_left (hCpos C) (Nat.cast_nonneg (α:=ℝ) U),Nat.cast_nonneg (α:=ℝ) b]
  have hB : ((big H:ℕ):ℝ)+1 ≤ mainSpaceBound G b := by
    apply le_trans _ (absorb_prod 1000001 D 6 b hb)
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) H) hH 6
    have hh1 := one_le_pow₀ (hCpos D) (n:=6); simp [big]; nlinarith only [hh,hh1]
  have hpoly := (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hB I) (Nat.cast_nonneg (α:=ℝ) I)).trans (absorb_prod I G I b hb)
  change polyBound I (big H) ≤ mainSpaceBound P b at hpoly
  let X := mainSpaceBound Z b
  have hx : 1 ≤ X := hCpos Z
  have pX : polyBound I (big H) ≤ X := hpoly.trans (mono _ _ (le_max_left ..))
  have CX : mainSpaceBound C b ≤ X := mono _ _ ((le_max_left C D).trans (le_max_right ..))
  have HX : (H:ℝ) ≤ X := hH.trans (mono _ _ ((le_max_right C D).trans (le_max_right ..)))
  have tX : τ ≤ X := (mono _ _ ((le_max_left J Cj).trans (le_max_right ..))).trans CX
  have sX : σ ≤ X := ((hCj p 0 (by omega) (by omega)).1).trans ((mono _ _ ((le_max_right J Cj).trans (le_max_right ..))).trans CX)
  have pp : mainSpaceBound P b ≤ X := mono _ _ (le_max_left ..)
  have term : polyBound I (big H)+(I:ℝ)*(τ+σ+1) ≤ (1+3*(I:ℝ))*X := by nlinarith only [pX,mul_le_mul_of_nonneg_left (show τ+σ+1 ≤ 3*X by linarith) (Nat.cast_nonneg (α:=ℝ) I)]
  have h3 := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) H) HX 3
  have h31 := one_le_pow₀ hx (n:=3)
  have nr : ((3*H^3+1:ℕ):ℝ) ≤ 4*X^3 := by push_cast; linarith
  have target := absorb_prod (4*(1+3*I)) Z 4 b hb
  change _ ≤ (mainSpaceBound _ _) at target
  constructor
  · apply le_trans _ target; have hmul := mul_le_mul nr term (by unfold polyBound; dsimp [τ,σ,mainSpaceBound,polyBound]; positivity) (by positivity); push_cast; push_cast at hmul; dsimp [X] at *; nlinarith only [hmul]
  · apply le_trans _ target; have h0 : 0 ≤ τ := by dsimp [τ,mainSpaceBound]; positivity
    have t' : polyBound I (big H)+(I:ℝ)*(σ+1) ≤ (1+3*(I:ℝ))*X := by nlinarith only [term,mul_nonneg (Nat.cast_nonneg (α:=ℝ) I) h0]
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (by decide : 1 ≤ 4)) (show 0 ≤ 1+3*(I:ℝ) by positivity)
    simp only [pow_one] at hh; push_cast; dsimp [X] at *; nlinarith only [t',hh,mul_nonneg (show 0 ≤ 1+3*(I:ℝ) by positivity) (pow_nonneg (by positivity : 0 ≤ mainSpaceBound Z b) 4)]

end DetDLP.ECEnumGrowth

end

section
set_option autoImplicit false
open DetDLP DetDLP.M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open DetDLP.ECEnumGrowth DetDLP.ECEnumBounds DetDLP.ECEnumTrace DetDLP.ECEnumRows DetDLP.ECEnumStep
set_option maxHeartbeats 1500000
private theorem branchTrace (U : ℕ) (hU : ∀ w, (ECEnumSmall.smallOut w).length ≤ U) (p : ℕ) [Fact p.Prime] (hp : 3 < p) (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (L : Option (ℕ × ECSeed p (blockCount (bitLen p)))) (ok : m89_ec_plan_ok E L) :
    let b := bitLen p; let m := blockCount b
    let sz := planSize E L
    let H := polybase b + sz + U + 10; let a := arg E L
    ∃ (F : Fin m → List E.toAffine.Point) (n : ℕ), (∀ i, (F i).Nodup ∧ (F i).toFinset = m89_ec_plan_block E L i) ∧ a.length ≤ H ∧ n ≤ 3*H^3 ∧ Trace (valid b) (big H) (encodeECFactorBlocks F) n (step (pair a [])) := by
  intro b m sz H a
  have hH : 10 ≤ H := by dsimp only [H]; omega
  have bigH : 2*H+1 ≤ big H := by unfold big; have h1 := Nat.pow_le_pow_right (by omega : 0 < H) (by decide : 1 ≤ 6); simp only [pow_one] at h1; omega
  cases L with
  | none =>
    obtain ⟨F,hs,he⟩ := ECEnumSmall.smallOut_spec hp E ok
    have hs0 : (arg E (none : Option (ℕ × ECSeed p m))).length ≤ H := (small_length (E:=E)).trans (show polybase b ≤ H by dsimp only [H]; omega)
    refine ⟨F,0,hs,hs0,by omega,?_⟩
    have hd : a.headD false = true := rfl
    have hplan : (plan a).headD false = false := by simp [a,m89_ec_plan_word]
    simp only [step_pair,ctrl,hd,if_true,start,hplan,Bool.false_eq_true,if_false]; rw [show base a = encodeCurveInput p E from base_arg _,he]
    apply Trace.stop; have := hU (encodeCurveInput p E); rw [he] at this; have hUH : U ≤ H := by dsimp only [H]; omega
    omega
  | some v =>
    obtain ⟨T,S⟩ := v
    obtain ⟨h1,h2,h3,h4,h5,h6,h7⟩ := lengths ok
    have hpoly : polybase b ≤ H := by dsimp [H]; omega
    obtain ⟨F,n,hF,hn,htr⟩ := traces hp ok H hH (h1.trans hpoly) (h2.trans hpoly) (h3.trans hpoly) (h4.trans hpoly) (h5.trans hpoly) (h6.trans hpoly) (by dsimp [H,sz,planSize]; omega)
    exact ⟨F,n,hF,h1.trans hpoly,hn,htr⟩


theorem solution : CountOracle → ∃ (M : PrimitiveMachine) (o : Fin M.tapeCount) (K : ℕ),
    ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic], 
      let b := bitLen p; let m := blockCount b
      ∀ L : Option (ℕ × ECSeed p m), m89_ec_plan_ok E L → ∃ F : Fin m → List E.toAffine.Point,
        (∀ i, (F i).Nodup ∧ (F i).toFinset = m89_ec_plan_block E L i) ∧
        RunsWithin M o (Encoding.encodeList id [(encodeCurveInput p E),m89_ec_plan_word L]) (encodeECFactorBlocks F) (mainSpaceBound K b) (mainSpaceBound K b) := by
  classical
  rintro ⟨O,o,J,oracle⟩
  obtain ⟨M,out,I,hI,run⟩ := m89_polyT_oracle_loop step step_poly O o
  obtain ⟨U,hU⟩ := ECEnumSmall.smallOut_bound
  obtain ⟨K,hK⟩ := resources U I J
  refine ⟨M,out,K,?_⟩
  intro p inst hp E el b m L ok
  let sz := planSize E L
  let H := polybase b + sz + U + 10
  let a := arg E L
  let τ := mainSpaceBound J b; let σ := polyBound J b
  have tpos : 0 ≤ τ := by dsimp [τ,mainSpaceBound]; positivity
  have spos : 0 ≤ σ := by dsimp [σ,polyBound]; positivity
  have res := hK p hp E L ok
  change ((3*H^3+1:ℕ):ℝ)*(polyBound I (big H)+(I:ℝ)*(τ+σ+1)) ≤ mainSpaceBound K b ∧ polyBound I (big H)+(I:ℝ)*(σ+1) ≤ mainSpaceBound K b at res
  have yes : ∀ q ans, valid b q ans → RunsWithin O o q ans τ σ := by rintro q _ ⟨n,h,rfl⟩; exact oracle _ _ _ h
  have hH : 10 ≤ H := by dsimp only [H]; omega
  have bigH : 2*H+1 ≤ big H := by unfold big; have h1 := Nat.pow_le_pow_right (by omega : 0 < H) (by decide : 1 ≤ 6); simp only [pow_one] at h1; omega
  have go (F : Fin m → List E.toAffine.Point) (n : ℕ) (hlen : a.length ≤ H) (hn : n ≤ 3*H^3)
      (tr : Trace (valid b) (big H) (encodeECFactorBlocks F) n (step (pair a []))) :
      RunsWithin M out a (encodeECFactorBlocks F) (mainSpaceBound K b) (mainSpaceBound K b) := by
    have hr := to_rounds O o τ σ yes tr (by simp only [pair_len,List.length_nil,Nat.add_zero]; omega)
    have r := run τ σ tpos spos (n+1) (big H) a (encodeECFactorBlocks F) (by omega) hr
    apply PolyTBridge.runsWithin_mono_local r _ res.2
    apply le_trans _ res.1
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hn 1) (by unfold polyBound; positivity)
  obtain ⟨F,n,hF,hlen,hn,tr⟩ := branchTrace U hU p hp E L ok
  exact ⟨F,hF,go F n hlen hn tr⟩


end

#print axioms solution
