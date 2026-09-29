-- Prove2me | solution 1 for Freiman.trunk_bindings_00_000_100
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:16:24.822249+00:00
-- url     : https://prove2.me/submissions/14d63d30-9e14-4481-9807-14626e29c0fb

import Definitions.Def_Freiman_trunkFast
import Theorems.Thm_Freiman_trunkFast_correctness
set_option Elab.async false
open Freiman Freiman.TrunkFast
private def intCode (z : ℤ) : ℕ := if z < 0 then 2*z.natAbs+1 else 2*z.natAbs
private def proj (b : CertBound) : ℕ :=
  [b.lower.toNat,b.strict.toNat,intCode b.threshold.c.a.num,b.threshold.c.a.den,
   intCode b.threshold.x0.a.num,b.threshold.x0.a.den,intCode b.threshold.c.b.num,
   b.threshold.c.b.den,intCode b.threshold.x0.b.num,b.threshold.x0.b.den].foldl
    (fun acc n => ((acc+n+17)*(acc+n+17)+3*acc) % 1000000007) 7
private def fingerprint (bs : List CertBound) : ℕ := ((bs.map proj).toFinset.sum id)

private theorem fingerprint_congr {cs bs : List CertBound} (heq : cs.toFinset = bs.toFinset) :
    fingerprint cs = fingerprint bs := by
  have hm : ∀ b, b ∈ cs ↔ b ∈ bs := by
    intro b
    have h := congrArg (fun s : Finset CertBound => b ∈ s) heq
    simpa using Iff.of_eq h
  have hi : (cs.map proj).toFinset = (bs.map proj).toFinset := by
    ext z
    simp only [List.mem_toFinset,List.mem_map,hm]
  exact congrArg (fun s : Finset ℕ => s.sum id) hi
private theorem parents_of_fingerprints (raw : List (List CertBound))
    (h : (raw.map fingerprint).Nodup) : raw.Pairwise (fun cs bs => cs.toFinset ≠ bs.toFinset) := by
  have h' : raw.Pairwise (fun cs bs => fingerprint cs ≠ fingerprint bs) := List.pairwise_map.mp h
  exact h'.imp fun hne heq => hne (fingerprint_congr heq)
private def rawParent (a b : List CertBound × LowerHistoryComparison) : Option (List CertBound) :=
  let base := a.1 ++ b.1 ++ [lowerHistoryHN,lowerHistoryZero]
  match a.2,b.2 with
  | .impossible,_ | _,.impossible => none
  | .automatic,.automatic => some base
  | .bound g,.automatic | .automatic,.bound g => some (g::base)
  | .bound g,.bound h => some (g::h::base)
private def branchCode (a : List CertBound × LowerHistoryComparison) : List ℕ × Option (Option ℕ) :=
  (a.1.map proj, match a.2 with
    | .impossible => none
    | .automatic => some none
    | .bound b => some (some (proj b)))
private def parentCode (hn zero : ℕ) (a b : List ℕ × Option (Option ℕ)) : Option (List ℕ) :=
  match a.2,b.2 with
  | none,_ | _,none => none
  | some ga,some gb => some (ga.toList ++ gb.toList ++ a.1 ++ b.1 ++ [hn,zero])
private theorem parentCode_map (a b : List CertBound × LowerHistoryComparison) :
    (rawParent a b).map (List.map proj) = parentCode (proj lowerHistoryHN) (proj lowerHistoryZero) (branchCode a) (branchCode b) := by
  rcases a with ⟨ca,ga⟩
  rcases b with ⟨cb,gb⟩
  cases ga <;> cases gb <;> simp [rawParent,parentCode,branchCode,List.map_append,List.append_assoc]
private theorem rawCodes_map (A B : List (List CertBound × LowerHistoryComparison)) :
    (A.flatMap (fun a => B.filterMap (rawParent a))).map (List.map proj) =
    (A.map branchCode).flatMap (fun a => (B.map branchCode).filterMap (parentCode (proj lowerHistoryHN) (proj lowerHistoryZero) a)) := by
  simp only [List.map_flatMap,List.map_filterMap,List.flatMap_map,List.filterMap_map,Function.comp_apply]
  apply congrArg (fun f => A.flatMap f)
  funext a
  apply congrArg (fun f => B.filterMap f)
  funext b
  exact parentCode_map a b
private theorem trunkCodes_map (C : LowerHistoryContext) :
    (trunkRawParents C).map (List.map proj) =
    ((trunkBranches C ⟨([2],[]),true,([1],[]),false,false,[]⟩).map branchCode).flatMap (fun a =>
    ((trunkBranches C ⟨([1],[]),true,([2],[]),false,false,[]⟩).map branchCode).filterMap (parentCode (proj lowerHistoryHN) (proj lowerHistoryZero) a)) := by
  exact rawCodes_map _ _

private def codesA0 : List (List ℕ × Option (Option ℕ)) := [([112911326, 882722351, 131368818, 335455726], some (some 948335893)),
 ([112911326, 882722351, 131368818, 46223616], some (some 626279719)),
 ([112911326, 882722351, 624295141, 16305415], some (some 948335893)),
 ([112911326, 882722351, 624295141, 58036967], some (some 102443919)),
 ([112911326, 991976176], some (some 948335893)),
 ([728891584, 60072750, 649066977, 882722351, 131368818, 335455726], some (some 948335893)),
 ([728891584, 60072750, 649066977, 882722351, 131368818, 46223616], some (some 626279719)),
 ([728891584, 60072750, 649066977, 882722351, 624295141, 16305415], some (some 948335893)),
 ([728891584, 60072750, 649066977, 882722351, 624295141, 58036967], some (some 102443919)),
 ([728891584, 60072750, 649066977, 991976176], some (some 948335893)),
 ([728891584, 60072750, 595767334, 882722351, 131368818, 335455726], some (some 690199589)),
 ([728891584, 60072750, 595767334, 882722351, 131368818, 46223616], some (some 416338889)),
 ([728891584, 60072750, 595767334, 882722351, 624295141, 16305415], some (some 690199589)),
 ([728891584, 60072750, 595767334, 882722351, 624295141, 58036967], some (some 609086174)),
 ([728891584, 60072750, 595767334, 991976176], some (some 690199589)),
 ([728891584, 476573349, 881768834, 882722351, 131368818, 335455726], some (some 948335893)),
 ([728891584, 476573349, 881768834, 882722351, 131368818, 46223616], some (some 626279719)),
 ([728891584, 476573349, 881768834, 882722351, 624295141, 16305415], some (some 948335893)),
 ([728891584, 476573349, 881768834, 882722351, 624295141, 58036967], some (some 102443919)),
 ([728891584, 476573349, 881768834, 991976176], some (some 948335893)),
 ([728891584, 476573349, 159503643, 882722351, 131368818, 335455726], some (some 507666506)),
 ([728891584, 476573349, 159503643, 882722351, 131368818, 46223616], some (some 753260783)),
 ([728891584, 476573349, 159503643, 882722351, 624295141, 16305415], some (some 507666506)),
 ([728891584, 476573349, 159503643, 882722351, 624295141, 58036967], some (some 21298099)),
 ([728891584, 476573349, 159503643, 991976176], some (some 507666506))]
private def codesB0 : List (List ℕ × Option (Option ℕ)) := [([882722351, 112911326, 475598846, 413245293], some none),
 ([882722351, 112911326, 475598846, 250783862], some none),
 ([882722351, 112911326, 18672300, 970110223], some none),
 ([882722351, 112911326, 18672300, 961625388], some none),
 ([882722351, 728891584], some none),
 ([991976176, 466397207, 55717250, 112911326, 475598846, 413245293], some none),
 ([991976176, 466397207, 55717250, 112911326, 475598846, 250783862], some none),
 ([991976176, 466397207, 55717250, 112911326, 18672300, 970110223], some none),
 ([991976176, 466397207, 55717250, 112911326, 18672300, 961625388], some none),
 ([991976176, 466397207, 55717250, 728891584], some none),
 ([991976176, 466397207, 649614909, 112911326, 475598846, 413245293], some none),
 ([991976176, 466397207, 649614909, 112911326, 475598846, 250783862], some none),
 ([991976176, 466397207, 649614909, 112911326, 18672300, 970110223], some none),
 ([991976176, 466397207, 649614909, 112911326, 18672300, 961625388], some none),
 ([991976176, 466397207, 649614909, 728891584], some none),
 ([991976176, 827878947, 143171926, 112911326, 475598846, 413245293], some none),
 ([991976176, 827878947, 143171926, 112911326, 475598846, 250783862], some none),
 ([991976176, 827878947, 143171926, 112911326, 18672300, 970110223], some none),
 ([991976176, 827878947, 143171926, 112911326, 18672300, 961625388], some none),
 ([991976176, 827878947, 143171926, 728891584], some none),
 ([991976176, 827878947, 222803470, 112911326, 475598846, 413245293], some none),
 ([991976176, 827878947, 222803470, 112911326, 475598846, 250783862], some none),
 ([991976176, 827878947, 222803470, 112911326, 18672300, 970110223], some none),
 ([991976176, 827878947, 222803470, 112911326, 18672300, 961625388], some none),
 ([991976176, 827878947, 222803470, 728891584], some none)]
private theorem hHN : proj lowerHistoryHN = 466397207 := by decide +kernel
private theorem hZero : proj lowerHistoryZero = 559802771 := by decide +kernel

private theorem hA0 : (trunkBranches (trunkCatalog.states 0).context ⟨([2],[]),true,([1],[]),false,false,[]⟩).map branchCode = codesA0 := by
  decide +kernel
private theorem hB0 : (trunkBranches (trunkCatalog.states 0).context ⟨([1],[]),true,([2],[]),false,false,[]⟩).map branchCode = codesB0 := by
  decide +kernel
private def fprints0 : List ℕ := [4325838231, 4163376800, 4425776615, 4417291780, 4165885676, 5373531657, 5211070226, 5473470041, 5464985206, 5213579102, 5967429316, 5804967885, 6067367700, 6058882865, 5807476761, 6288865280, 6126403849, 6388803664, 6380318829, 6128912725, 6368496824, 6206035393, 6468435208, 6459950373, 6208544269, 3714549947, 3552088516, 3814488331, 3806003496, 3554597392, 4762243373, 4599781942, 4862181757, 4853696922, 4602290818, 5356141032, 5193679601, 5456079416, 5447594581, 5196188477, 5677576996, 5515115565, 5777515380, 5769030545, 5517624441, 5757208540, 5594747109, 5857146924, 5848662089, 5597255985, 4499614243, 4337152812, 4599552627, 4591067792, 4339661688, 5547307669, 5384846238, 5647246053, 5638761218, 5387355114, 6141205328, 5978743897, 6241143712, 6232658877, 5981252773, 6462641292, 6300179861, 6562579676, 6554094841, 6302688737, 6542272836, 6379811405, 6642211220, 6633726385, 6382320281, 3695453821, 3532992390, 3795392205, 3786907370, 3535501266, 4743147247, 4580685816, 4843085631, 4834600796, 4583194692, 5337044906, 5174583475, 5436983290, 5428498455, 5177092351, 5658480870, 5496019439, 5758419254, 5749934419, 5498528315, 5738112414, 5575650983, 5838050798, 5829565963, 5578159859, 4850989863, 4688528432, 4950928247, 4942443412, 4691037308, 4023984762, 3861523331, 4123923146, 4115438311, 3864032207, 4617882421, 4455420990, 4717820805, 4709335970, 4457929866, 4939318385, 4776856954, 5039256769, 5030771934, 4779365830, 5018949929, 4856488498, 5118888313, 5110403478, 4858997374, 5763869542, 5601408111, 5863807926, 5855323091, 4762114077, 6811562968, 6649101537, 6911501352, 6903016517, 5809807503, 7405460627, 7242999196, 7505399011, 7496914176, 6403705162, 7726896591, 7564435160, 7826834975, 7818350140, 6725141126, 7806528135, 7644066704, 7906466519, 7897981684, 6804772670, 5152581258, 4990119827, 5252519642, 5244034807, 4150825793, 6200274684, 6037813253, 6300213068, 6291728233, 5198519219, 6794172343, 6631710912, 6894110727, 6885625892, 5792416878, 7115608307, 6953146876, 7215546691, 7207061856, 6113852842, 7195239851, 7032778420, 7295178235, 7286693400, 6193484386, 5937645554, 5775184123, 6037583938, 6029099103, 4935890089, 6985338980, 6822877549, 7085277364, 7076792529, 5983583515, 7579236639, 7416775208, 7679175023, 7670690188, 6577481174, 7900672603, 7738211172, 8000610987, 7992126152, 6898917138, 7980304147, 7817842716, 8080242531, 8071757696, 6978548682, 5133485132, 4971023701, 5233423516, 5224938681, 4131729667, 6181178558, 6018717127, 6281116942, 6272632107, 5179423093, 6775076217, 6612614786, 6875014601, 6866529766, 5773320752, 7096512181, 6934050750, 7196450565, 7187965730, 6094756716, 7176143725, 7013682294, 7276082109, 7267597274, 6174388260, 6289021174, 6126559743, 6388959558, 6380474723, 5287265709, 5462016073, 5299554642, 5561954457, 5553469622, 4460260608, 6055913732, 5893452301, 6155852116, 6147367281, 5054158267, 6377349696, 6214888265, 6477288080, 6468803245, 5375594231, 6456981240, 6294519809, 6556919624, 6548434789, 5455225775, 5452433595, 5289972164, 5552371979, 5543887144, 4450678130, 6500127021, 6337665590, 6600065405, 6591580570, 5498371556, 7094024680, 6931563249, 7193963064, 7185478229, 6092269215, 7415460644, 7252999213, 7515399028, 7506914193, 6413705179, 7495092188, 7332630757, 7595030572, 7586545737, 6493336723, 4889340785, 4726879354, 4989279169, 4980794334, 3887585320, 5937034211, 5774572780, 6036972595, 6028487760, 4935278746, 6530931870, 6368470439, 6630870254, 6622385419, 5529176405, 6852367834, 6689906403, 6952306218, 6943821383, 5850612369, 6931999378, 6769537947, 7031937762, 7023452927, 5930243913, 5626209607, 5463748176, 5726147991, 5717663156, 4624454142, 6673903033, 6511441602, 6773841417, 6765356582, 5672147568, 7267800692, 7105339261, 7367739076, 7359254241, 6266045227, 7589236656, 7426775225, 7689175040, 7680690205, 6587481191, 7668868200, 7506406769, 7768806584, 7760321749, 6667112735, 5586827744, 5424366313, 5686766128, 5678281293, 4585072279, 6634521170, 6472059739, 6734459554, 6725974719, 5632765705, 7228418829, 7065957398, 7328357213, 7319872378, 6226663364, 7549854793, 7387393362, 7649793177, 7641308342, 6548099328, 7629486337, 7467024906, 7729424721, 7720939886, 6627730872, 5977585227, 5815123796, 6077523611, 6069038776, 4975829762, 5150580126, 4988118695, 5250518510, 5242033675, 4148824661, 5744477785, 5582016354, 5844416169, 5835931334, 4742722320, 6065913749, 5903452318, 6165852133, 6157367298, 5064158284, 6145545293, 5983083862, 6245483677, 6236998842, 5143789828, 6413071998, 6250610567, 6513010382, 6504525547, 5411316533, 7460765424, 7298303993, 7560703808, 7552218973, 6459009959, 8054663083, 7892201652, 8154601467, 8146116632, 7052907618, 8376099047, 8213637616, 8476037431, 8467552596, 7374343582, 8455730591, 8293269160, 8555668975, 8547184140, 7453975126, 5801783714, 5639322283, 5901722098, 5893237263, 4800028249, 6849477140, 6687015709, 6949415524, 6940930689, 5847721675, 7443374799, 7280913368, 7543313183, 7534828348, 6441619334, 7764810763, 7602349332, 7864749147, 7856264312, 6763055298, 7844442307, 7681980876, 7944380691, 7935895856, 6842686842, 6586848010, 6424386579, 6686786394, 6678301559, 5585092545, 7634541436, 7472080005, 7734479820, 7725994985, 6632785971, 8228439095, 8065977664, 8328377479, 8319892644, 7226683630, 8549875059, 8387413628, 8649813443, 8641328608, 7548119594, 8629506603, 8467045172, 8729444987, 8720960152, 7627751138, 5782687588, 5620226157, 5882625972, 5874141137, 4780932123, 6830381014, 6667919583, 6930319398, 6921834563, 5828625549, 7424278673, 7261817242, 7524217057, 7515732222, 6422523208, 7745714637, 7583253206, 7845653021, 7837168186, 6743959172, 7825346181, 7662884750, 7925284565, 7916799730, 6823590716, 6938223630, 6775762199, 7038162014, 7029677179, 5936468165, 6111218529, 5948757098, 6211156913, 6202672078, 5109463064, 6705116188, 6542654757, 6805054572, 6796569737, 5703360723, 7026552152, 6864090721, 7126490536, 7118005701, 6024796687, 7106183696, 6943722265, 7206122080, 7197637245, 6104428231, 5250137420, 5087675989, 5350075804, 5341590969, 4248381955, 6297830846, 6135369415, 6397769230, 6389284395, 5296075381, 6891728505, 6729267074, 6991666889, 6983182054, 5889973040, 7213164469, 7050703038, 7313102853, 7304618018, 6211409004, 7292796013, 7130334582, 7392734397, 7384249562, 6291040548, 5206499587, 5044038156, 5306437971, 5297953136, 4204744122, 6254193013, 6091731582, 6354131397, 6345646562, 5252437548, 6848090672, 6685629241, 6948029056, 6939544221, 5846335207, 7169526636, 7007065205, 7269465020, 7260980185, 6167771171, 7249158180, 7086696749, 7349096564, 7340611729, 6247402715, 5423913432, 5261452001, 5523851816, 5515366981, 4422157967, 6471606858, 6309145427, 6571545242, 6563060407, 5469851393, 7065504517, 6903043086, 7165442901, 7156958066, 6063749052, 7386940481, 7224479050, 7486878865, 7478394030, 6385185016, 7466572025, 7304110594, 7566510409, 7558025574, 6464816560, 4979276577, 4816815146, 5079214961, 5070730126, 3977521112, 6026970003, 5864508572, 6126908387, 6118423552, 5025214538, 6620867662, 6458406231, 6720806046, 6712321211, 5619112197, 6942303626, 6779842195, 7042242010, 7033757175, 5940548161, 7021935170, 6859473739, 7121873554, 7113388719, 6020179705, 5775289052, 5612827621, 5875227436, 5866742601, 4773533587, 4948283951, 4785822520, 5048222335, 5039737500, 3946528486, 5542181610, 5379720179, 5642119994, 5633635159, 4540426145, 5863617574, 5701156143, 5963555958, 5955071123, 4861862109, 5943249118, 5780787687, 6043187502, 6034702667, 4941493653]
private theorem hprints0 : (trunkRawParents (trunkCatalog.states 0).context).map fingerprint = fprints0 := by
  have hm (L : List (List CertBound)) :
      L.map fingerprint = (L.map (List.map proj)).map (fun cs => cs.toFinset.sum id) := by
    rw [List.map_map]; rfl
  rw [hm,trunkCodes_map,hA0,hB0,hHN,hZero]
  decide +kernel
private theorem hPar0 : trunkParents (trunkCatalog.states 0).context = trunkRawParents (trunkCatalog.states 0).context := by
  apply Freiman.trunkFast_correctness.1
  apply parents_of_fingerprints
  rw [hprints0]
  apply (List.perm_insertionSort (fun a b : ℕ => a ≤ b) fprints0).nodup_iff.mp
  have hs : (List.insertionSort (fun a b : ℕ => a ≤ b) fprints0).IsChain (fun a b => a < b) := by
    decide +kernel
  exact (List.isChain_iff_pairwise.mp hs).imp (fun h => Nat.ne_of_lt h)


set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
private def decodeThresholdBound (b : ℕ × Bool × Bool) : CertBound :=
  ⟨b.2.1,b.2.2,(fastBound b.1).threshold⟩
private def decodeGoalBranch (a : List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) : List CertBound × LowerHistoryComparison :=
  (a.1.map decodeThresholdBound, match a.2 with
    | none => .impossible
    | some none => .automatic
    | some (some b) => .bound (decodeThresholdBound b))
private def thresholdClasses : Array ℕ := #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 2, 6, 13, 13, 3, 10, 17, 18, 17, 20, 18, 20, 23, 9, 4, 26, 27, 26, 29, 30, 31, 32, 33,
 34, 31, 36, 37, 32, 39, 37, 41, 33, 43, 44, 45, 46, 45, 48, 49, 50, 51, 52, 53, 52, 55, 56, 57, 56, 59, 51, 61, 62, 50,
 64, 65, 64, 67, 68, 69, 70, 71, 72, 73, 70, 75, 72, 77, 75, 69, 80, 81, 82, 83, 83, 85, 86, 87, 88, 89, 90, 91, 92, 90,
 30, 95, 95, 97, 91, 99, 100, 101, 102, 89, 104, 102, 106, 107, 108, 109, 110, 111, 112, 113, 114, 108, 112, 117, 117,
 119, 113, 121, 122, 123, 109, 125, 126, 125, 128, 129, 130, 110, 132, 133, 133, 135, 136, 132, 136, 139, 1, 23, 27,
 143, 29, 145, 146, 147, 148, 147, 150, 151, 152, 153, 154, 155, 156, 157, 155, 159, 160, 156, 162, 162, 164, 165, 166,
 8, 168, 168, 143, 145, 146, 148, 150, 151, 176, 177, 7, 179, 180, 181, 182, 183, 184, 181, 186, 187, 186, 189, 184,
 191, 189, 179, 194, 195, 196, 197, 182, 199, 197, 201, 202, 183, 204, 205, 206, 205, 208, 206, 210, 208, 212, 213, 210,
 215, 213, 217, 218, 219, 220, 221, 222, 223, 224, 225, 176, 227, 228, 228, 230, 231, 232, 233, 234, 235, 236, 231, 238,
 239, 236, 239, 242, 234, 233, 245, 246, 235, 248, 249, 248, 251, 249, 253, 254, 251, 254, 257, 246, 259, 260, 261, 262,
 263, 264, 263, 266, 259, 261, 269, 269, 271, 260, 273, 274, 275, 262, 274, 275, 279, 280, 280, 282, 283, 279, 285, 283,
 287, 288, 288, 290, 291, 292, 291, 294, 177, 296, 297, 298, 299, 300, 301, 299, 303, 304, 303, 301, 307, 307, 309, 310,
 311, 312, 298, 314, 315, 316, 297, 318, 319, 320, 321, 322, 323, 321, 325, 322, 327, 325, 320, 319, 331, 332, 332, 334,
 335, 336, 337, 331, 337, 340, 341, 342, 343, 344, 345, 346, 347, 346, 349, 350, 349, 352, 347, 354, 352, 356, 357, 358,
 343, 360, 361, 362, 344, 364, 365, 366, 366, 365, 369, 370, 370, 372, 373, 369, 375, 373, 377, 378, 379, 380, 381, 381,
 383, 384, 385, 383, 384, 388, 388, 390, 391, 377, 393, 394, 395, 379, 395, 398, 399, 400, 380, 402, 403, 404, 405, 406,
 407, 403, 409, 406, 411, 409, 404, 414, 415, 405, 414, 418, 419, 420, 421, 415, 421, 424, 425, 426, 427, 428, 429, 430,
 431, 432, 428, 434, 427, 436, 430, 436, 439, 432, 441, 431, 443, 444, 445, 446, 447, 444, 449, 445, 451, 449, 446, 443,
 455, 456, 456, 458, 459, 460, 461, 455, 461, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 476,
 479, 479, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 490, 494, 495, 496, 497, 497, 499, 500, 501, 502,
 503, 504, 505, 506, 507, 296, 509, 510, 511, 512, 513, 510, 515, 516, 517, 511, 519, 520, 519, 522, 523, 524, 525, 526,
 526, 528, 529, 525, 531, 529, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 550,
 551, 551]
private def thresholdClass (id : ℕ) : ℕ := thresholdClasses[id-1]?.getD 0

private def classValidIds : List ℕ := [1, 2, 6, 9, 15, 3, 16, 10, 23, 4, 14, 27, 19, 20, 21, 25, 31, 32, 34, 40, 46, 88, 29, 92, 94, 98, 102, 103, 108, 112, 111, 118, 121, 126, 130, 134, 136, 137, 140, 26, 28, 144, 30, 110, 152, 157, 162, 161, 164, 17, 167, 8, 22, 171, 90, 7, 170, 143, 53, 55, 60, 64, 63, 18, 147, 176]
private theorem thresholdClass_key : ∀ i ∈ classValidIds,
    i = thresholdClass i ∨ (fastBound i).threshold = (fastBound (thresholdClass i)).threshold := by decide +kernel
private theorem threshold_class_of_range (i : ℕ) (hi : i ∈ classValidIds) :
    (fastBound i).threshold = (fastBound (thresholdClass i)).threshold := by
  rcases thresholdClass_key i hi with he | he
  · rw [← he]
  · exact he
private def codeUseBounds (w : TrunkWitness) (l u : ℕ × Bool × Bool) : Prop :=
  l.2.1 = true ∧ u.2.1 = false ∧
  w.lowerId ∈ classValidIds ∧ w.upperId ∈ classValidIds ∧
  l.1 = thresholdClass w.lowerId ∧ u.1 = thresholdClass w.upperId ∧
  ((w.diagonal = 0 ∧ 0 < w.margin) ∨ l.2.2 = true ∨ u.2.2 = true)
private theorem codeUseBounds_sound (w : TrunkWitness) (l u : ℕ × Bool × Bool)
    (h : codeUseBounds w l u) : trunkUseBoundsFast w (decodeThresholdBound l) (decodeThresholdBound u) := by
  rcases h with ⟨hl,hu,hll,hul,hle,hue,hs⟩
  refine ⟨hl,hu,?_,?_,hs⟩
  · change (fastBound l.1).threshold = (fastBound w.lowerId).threshold
    rw [hle,← threshold_class_of_range w.lowerId hll]
  · change (fastBound u.1).threshold = (fastBound w.upperId).threshold
    rw [hue,← threshold_class_of_range w.upperId hul]
private def codeLeafBound (R : CertRectangle) (bs : List (ℕ × Bool × Bool)) (id : ℕ) (sign : ℤ) : Prop :=
  0 < id ∧ id ≤ 8656 ∧
  (fastWitness id).diagonal = sign ∧
  section14RectangleContains (fastWitness id).rectangle R ∧
  ∃ l ∈ bs, ∃ u ∈ bs, codeUseBounds (fastWitness id) l u
private theorem codeLeafBound_sound (R : CertRectangle) (bs : List (ℕ × Bool × Bool)) (id : ℕ) (sign : ℤ)
    (h : codeLeafBound R bs id sign) : trunkLeafBoundFast R (bs.map decodeThresholdBound) id sign := by
  rcases h with ⟨hlo,hhi,hdiag,hrect,l,hl,u,hu,huse⟩
  exact ⟨hlo,hhi,hdiag,hrect,decodeThresholdBound l,List.mem_map.mpr ⟨l,hl,rfl⟩,
    decodeThresholdBound u,List.mem_map.mpr ⟨u,hu,rfl⟩,codeUseBounds_sound _ _ _ huse⟩
private def codeTreeBound (R : CertRectangle) (bs : List (ℕ × Bool × Bool)) : TrunkTree → Prop
  | .pair id => codeLeafBound R bs id 0
  | .split axis left right =>
    codeTreeBound (trunkRectangleHalf R axis false) bs left ∧
    codeTreeBound (trunkRectangleHalf R axis true) bs right
  | .diagonal negative positive => codeLeafBound R bs negative (-1) ∧ codeLeafBound R bs positive 1
  | .boundary => trunkBoundaryBound R (bs.map decodeThresholdBound)
private instance decCodeTreeBound (R : CertRectangle) (bs : List (ℕ × Bool × Bool)) :
    ∀ t : TrunkTree, Decidable (codeTreeBound R bs t)
  | .pair id => by unfold codeTreeBound codeLeafBound codeUseBounds section14RectangleContains; infer_instance
  | .split axis left right => by
      unfold codeTreeBound
      have := decCodeTreeBound (trunkRectangleHalf R axis false) bs left
      have := decCodeTreeBound (trunkRectangleHalf R axis true) bs right
      infer_instance
  | .diagonal negative positive => by
      unfold codeTreeBound codeLeafBound codeUseBounds section14RectangleContains
      infer_instance
  | .boundary => by unfold codeTreeBound trunkBoundaryBound certThresholdDataValid; infer_instance
private theorem codeTreeBound_sound (t : TrunkTree) (R : CertRectangle) (bs : List (ℕ × Bool × Bool))
    (h : codeTreeBound R bs t) : trunkTreeBoundFast R (bs.map decodeThresholdBound) t := by
  induction t generalizing R with
  | pair id => exact codeLeafBound_sound _ _ _ _ h
  | split axis left right ihl ihr => exact ⟨ihl _ h.1,ihr _ h.2⟩
  | diagonal negative positive => exact ⟨codeLeafBound_sound _ _ _ _ h.1,codeLeafBound_sound _ _ _ _ h.2⟩
  | boundary => exact h
private def codeComplement (b : ℕ × Bool × Bool) : ℕ × Bool × Bool := (b.1,!b.2.1,!b.2.2)
private theorem decodeComplement (b : ℕ × Bool × Bool) :
    decodeThresholdBound (codeComplement b) = lowerHistoryComplement (decodeThresholdBound b) := rfl
private def codeResidual (parents : List (List (ℕ × Bool × Bool))) (cuts : List (ℕ × Bool × Bool))
    (goals : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))))
    (parent : ℕ) (branch : ℤ) : List (ℕ × Bool × Bool) :=
  let b := goals[branch.toNat]?.getD ([],none)
  cuts ++ parents[parent]?.getD [] ++ b.1 ++
    match b.2 with | some (some a) => [codeComplement a] | _ => []
private theorem codedBranch_eq (S : TrunkState) (pi goal : ℕ) (branch : ℤ)
    (codes : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))))
    (he : trunkGoalBranches S pi goal = codes.map decodeGoalBranch) :
    trunkBranch S pi goal branch = decodeGoalBranch (codes[branch.toNat]?.getD ([],none)) := by
  unfold trunkBranch
  rw [he,List.getElem?_map]
  exact Option.getD_map decodeGoalBranch ([],none) codes[branch.toNat]?
private theorem codedParent_eq (codes : List (List (ℕ × Bool × Bool))) (i : ℕ) :
    (codes.map (List.map decodeThresholdBound))[i]?.getD [] =
      (codes[i]?.getD []).map decodeThresholdBound := by
  rw [List.getElem?_map]
  exact Option.getD_map (List.map decodeThresholdBound) [] codes[i]?
private theorem codeResidual_eq (S : TrunkState) (pi parent goal : ℕ) (branch : ℤ)
    (parents : List (List (ℕ × Bool × Bool))) (cuts : List (ℕ × Bool × Bool))
    (goals : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))))
    (hpar : trunkRawParents S.context = parents.map (List.map decodeThresholdBound))
    (hcut : (trunkPlanAt S pi).cuts = cuts.map decodeThresholdBound)
    (hgoal : trunkGoalBranches S pi goal = goals.map decodeGoalBranch) :
    trunkResidualFast S pi parent goal branch = (codeResidual parents cuts goals parent branch).map decodeThresholdBound := by
  unfold trunkResidualFast codeResidual
  rw [hcut,hpar,codedParent_eq,codedBranch_eq S pi goal branch goals hgoal]
  generalize goals[branch.toNat]?.getD ([],none) = b
  rcases b with ⟨bs,cmp⟩
  cases cmp with
  | none => simp [decodeGoalBranch,List.map_append]
  | some cmp =>
    cases cmp <;> simp [decodeGoalBranch,List.map_append,decodeComplement]
private def codeGroupValid (S : TrunkState) (parents : List (List (ℕ × Bool × Bool)))
    (cuts : ℕ → List (ℕ × Bool × Bool))
    (goals : ℕ → ℕ → List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))))
    (g : TrunkGroup) : Prop :=
  g.plan < (trunkSourcePlans S.context).length ∧ g.goal ≤ (trunkSpecs (trunkPlanAt S g.plan)).length ∧
  (∀ p ∈ g.parents, p < parents.length) ∧
  ∀ bt ∈ g.branches,
    ((g.goal = 0 ∧ bt.1 = -1) ∨ (0 < g.goal ∧ 0 ≤ bt.1 ∧ bt.1.toNat < (goals g.plan g.goal).length)) ∧
    ((goals g.plan g.goal)[bt.1.toNat]?.getD ([],none)).2 ≠ some none ∧
    ∀ p ∈ g.parents, codeTreeBound S.rectangle (codeResidual parents (cuts g.plan) (goals g.plan g.goal) p bt.1) bt.2
private theorem codeGroupValid_sound (k : Fin 16) (parents : List (List (ℕ × Bool × Bool)))
    (cuts : ℕ → List (ℕ × Bool × Bool))
    (goals : ℕ → ℕ → List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))))
    (g : TrunkGroup)
    (hpar : trunkRawParents (trunkCatalog.states k).context = parents.map (List.map decodeThresholdBound))
    (hcut : (trunkPlanAt (trunkCatalog.states k) g.plan).cuts = (cuts g.plan).map decodeThresholdBound)
    (hgoal : trunkGoalBranches (trunkCatalog.states k) g.plan g.goal = (goals g.plan g.goal).map decodeGoalBranch)
    (h : codeGroupValid (trunkCatalog.states k) parents cuts goals g) : trunkGroupValidFast k g := by
  rcases h with ⟨hp,hg,hparents,hb⟩
  refine ⟨hp,hg,?_,?_⟩
  · simpa only [hpar,List.length_map] using hparents
  · intro bt hbt
    obtain ⟨hr,ha,ht⟩ := hb bt hbt
    refine ⟨?_,?_,?_⟩
    · simpa only [hgoal,List.length_map] using hr
    · rw [codedBranch_eq _ _ _ _ _ hgoal]
      generalize he : (goals g.plan g.goal)[bt.1.toNat]?.getD ([],none) = b at *
      rcases b with ⟨bs,cmp⟩
      cases cmp with
      | none => simp [decodeGoalBranch]
      | some cmp =>
        cases cmp <;> simp_all [decodeGoalBranch]
    · intro p hpg
      rw [codeResidual_eq _ _ _ _ _ parents (cuts g.plan) (goals g.plan g.goal) hpar hcut hgoal]
      exact codeTreeBound_sound _ _ _ (ht p hpg)
private def codeHN : ℕ × Bool × Bool := (8, false, false)
private def codeZero : ℕ × Bool × Bool := (5, true, true)

private theorem hDecodeHN : decodeThresholdBound codeHN = lowerHistoryHN := by decide +kernel
private theorem hDecodeZero : decodeThresholdBound codeZero = lowerHistoryZero := by decide +kernel
private def codeRawParent (a b : List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) : Option (List (ℕ × Bool × Bool)) :=
  match a.2,b.2 with
  | none,_ | _,none => none
  | some ga,some gb => some (ga.toList ++ gb.toList ++ a.1 ++ b.1 ++ [codeHN,codeZero])
private theorem codeRawParent_map (a b : List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) :
    (codeRawParent a b).map (List.map decodeThresholdBound) = rawParent (decodeGoalBranch a) (decodeGoalBranch b) := by
  rcases a with ⟨ca,ga⟩
  rcases b with ⟨cb,gb⟩
  cases ga with
  | none => simp [codeRawParent,decodeGoalBranch,rawParent]
  | some ga =>
    cases gb with
    | none => cases ga <;> simp [codeRawParent,decodeGoalBranch,rawParent]
    | some gb =>
      cases ga <;> cases gb <;>
        simp [codeRawParent,decodeGoalBranch,rawParent,List.map_append,List.append_assoc,hDecodeHN,hDecodeZero]
private theorem codeParents_map (A B : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool)))) :
    (A.flatMap (fun a => B.filterMap (codeRawParent a))).map (List.map decodeThresholdBound) =
    (A.map decodeGoalBranch).flatMap (fun a => (B.map decodeGoalBranch).filterMap (rawParent a)) := by
  simp only [List.map_flatMap,List.map_filterMap,List.flatMap_map,List.filterMap_map,Function.comp_apply]
  apply congrArg (fun f => A.flatMap f)
  funext a
  apply congrArg (fun f => B.filterMap f)
  funext b
  exact codeRawParent_map a b
private def thresholdParentA0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(3, false, false), (10, false, false), (4, false, false), (9, false, true)], some (some (1, true, false))),
 ([(3, false, false), (10, false, false), (4, false, false), (9, true, false)], some (some (23, true, false))),
 ([(3, false, false), (10, false, false), (4, true, true), (26, true, true)], some (some (1, true, false))),
 ([(3, false, false), (10, false, false), (4, true, true), (26, false, false)], some (some (27, true, false))),
 ([(3, false, false), (10, true, true)], some (some (1, true, false))),
 ([(3, true, true), (30, false, false), (29, false, true), (10, false, false), (4, false, false), (9, false, true)],
  some (some (1, true, false))),
 ([(3, true, true), (30, false, false), (29, false, true), (10, false, false), (4, false, false), (9, true, false)],
  some (some (23, true, false))),
 ([(3, true, true), (30, false, false), (29, false, true), (10, false, false), (4, true, true), (26, true, true)],
  some (some (1, true, false))),
 ([(3, true, true), (30, false, false), (29, false, true), (10, false, false), (4, true, true), (26, false, false)],
  some (some (27, true, false))),
 ([(3, true, true), (30, false, false), (29, false, true), (10, true, true)], some (some (1, true, false))),
 ([(3, true, true), (30, false, false), (29, true, false), (10, false, false), (4, false, false), (9, false, true)],
  some (some (143, true, false))),
 ([(3, true, true), (30, false, false), (29, true, false), (10, false, false), (4, false, false), (9, true, false)],
  some (some (145, true, false))),
 ([(3, true, true), (30, false, false), (29, true, false), (10, false, false), (4, true, true), (26, true, true)],
  some (some (143, true, false))),
 ([(3, true, true), (30, false, false), (29, true, false), (10, false, false), (4, true, true), (26, false, false)],
  some (some (146, true, false))),
 ([(3, true, true), (30, false, false), (29, true, false), (10, true, true)], some (some (143, true, false))),
 ([(3, true, true), (30, true, true), (147, true, true), (10, false, false), (4, false, false), (9, false, true)],
  some (some (1, true, false))),
 ([(3, true, true), (30, true, true), (147, true, true), (10, false, false), (4, false, false), (9, true, false)],
  some (some (23, true, false))),
 ([(3, true, true), (30, true, true), (147, true, true), (10, false, false), (4, true, true), (26, true, true)],
  some (some (1, true, false))),
 ([(3, true, true), (30, true, true), (147, true, true), (10, false, false), (4, true, true), (26, false, false)],
  some (some (27, true, false))),
 ([(3, true, true), (30, true, true), (147, true, true), (10, true, true)], some (some (1, true, false))),
 ([(3, true, true), (30, true, true), (147, false, false), (10, false, false), (4, false, false), (9, false, true)],
  some (some (148, true, false))),
 ([(3, true, true), (30, true, true), (147, false, false), (10, false, false), (4, false, false), (9, true, false)],
  some (some (150, true, false))),
 ([(3, true, true), (30, true, true), (147, false, false), (10, false, false), (4, true, true), (26, true, true)],
  some (some (148, true, false))),
 ([(3, true, true), (30, true, true), (147, false, false), (10, false, false), (4, true, true), (26, false, false)],
  some (some (151, true, false))),
 ([(3, true, true), (30, true, true), (147, false, false), (10, true, true)], some (some (148, true, false)))]
private def thresholdParentB0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(10, false, false), (3, false, false), (6, false, false), (2, false, true)], some none),
 ([(10, false, false), (3, false, false), (6, false, false), (2, true, false)], some none),
 ([(10, false, false), (3, false, false), (6, true, true), (13, true, true)], some none),
 ([(10, false, false), (3, false, false), (6, true, true), (13, false, false)], some none),
 ([(10, false, false), (3, true, true)], some none),
 ([(10, true, true), (18, false, false), (17, false, true), (3, false, false), (6, false, false), (2, false, true)],
  some none),
 ([(10, true, true), (18, false, false), (17, false, true), (3, false, false), (6, false, false), (2, true, false)],
  some none),
 ([(10, true, true), (18, false, false), (17, false, true), (3, false, false), (6, true, true), (13, true, true)],
  some none),
 ([(10, true, true), (18, false, false), (17, false, true), (3, false, false), (6, true, true), (13, false, false)],
  some none),
 ([(10, true, true), (18, false, false), (17, false, true), (3, true, true)], some none),
 ([(10, true, true), (18, false, false), (17, true, false), (3, false, false), (6, false, false), (2, false, true)],
  some none),
 ([(10, true, true), (18, false, false), (17, true, false), (3, false, false), (6, false, false), (2, true, false)],
  some none),
 ([(10, true, true), (18, false, false), (17, true, false), (3, false, false), (6, true, true), (13, true, true)],
  some none),
 ([(10, true, true), (18, false, false), (17, true, false), (3, false, false), (6, true, true), (13, false, false)],
  some none),
 ([(10, true, true), (18, false, false), (17, true, false), (3, true, true)], some none),
 ([(10, true, true), (18, true, true), (20, true, true), (3, false, false), (6, false, false), (2, false, true)],
  some none),
 ([(10, true, true), (18, true, true), (20, true, true), (3, false, false), (6, false, false), (2, true, false)],
  some none),
 ([(10, true, true), (18, true, true), (20, true, true), (3, false, false), (6, true, true), (13, true, true)],
  some none),
 ([(10, true, true), (18, true, true), (20, true, true), (3, false, false), (6, true, true), (13, false, false)],
  some none),
 ([(10, true, true), (18, true, true), (20, true, true), (3, true, true)], some none),
 ([(10, true, true), (18, true, true), (20, false, false), (3, false, false), (6, false, false), (2, false, true)],
  some none),
 ([(10, true, true), (18, true, true), (20, false, false), (3, false, false), (6, false, false), (2, true, false)],
  some none),
 ([(10, true, true), (18, true, true), (20, false, false), (3, false, false), (6, true, true), (13, true, true)],
  some none),
 ([(10, true, true), (18, true, true), (20, false, false), (3, false, false), (6, true, true), (13, false, false)],
  some none),
 ([(10, true, true), (18, true, true), (20, false, false), (3, true, true)], some none)]

private def codedParents0 : List (List (ℕ × Bool × Bool)) :=
  thresholdParentA0.flatMap (fun a => thresholdParentB0.filterMap (codeRawParent a))
private theorem hThresholdParentA0 : trunkBranches (trunkCatalog.states 0).context ⟨([2],[]),true,([1],[]),false,false,[]⟩ = thresholdParentA0.map decodeGoalBranch := by decide +kernel
private theorem hThresholdParentB0 : trunkBranches (trunkCatalog.states 0).context ⟨([1],[]),true,([2],[]),false,false,[]⟩ = thresholdParentB0.map decodeGoalBranch := by decide +kernel
private theorem hCodedParents0 : trunkRawParents (trunkCatalog.states 0).context = codedParents0.map (List.map decodeThresholdBound) := by
  unfold trunkRawParents codedParents0
  rw [hThresholdParentA0,hThresholdParentB0,codeParents_map]
  rfl
private def goalCodes0_0_0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([], none)]
private def goalCodes0_0_2 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(10, false, false), (4, false, false), (33, false, true), (32, false, false), (31, false, true)],
  some (some (34, true, true))),
 ([(10, false, false), (4, false, false), (33, false, true), (32, false, false), (31, true, false)],
  some (some (36, true, true))),
 ([(10, false, false), (4, false, false), (33, false, true), (32, true, true), (37, true, true)],
  some (some (34, true, true))),
 ([(10, false, false), (4, false, false), (33, false, true), (32, true, true), (37, false, false)],
  some (some (39, true, true))),
 ([(10, false, false), (4, false, false), (33, true, false), (32, false, false), (31, false, true)],
  some (some (41, true, true))),
 ([(10, false, false), (4, false, false), (33, true, false), (32, false, false), (31, true, false)],
  some (some (43, true, true))),
 ([(10, false, false), (4, false, false), (33, true, false), (32, true, true), (37, true, true)],
  some (some (41, true, true))),
 ([(10, false, false), (4, false, false), (33, true, false), (32, true, true), (37, false, false)],
  some (some (44, true, true))),
 ([(10, false, false), (4, true, true), (45, true, true), (32, false, false), (31, false, true)],
  some (some (34, true, true))),
 ([(10, false, false), (4, true, true), (45, true, true), (32, false, false), (31, true, false)],
  some (some (36, true, true))),
 ([(10, false, false), (4, true, true), (45, true, true), (32, true, true), (37, true, true)],
  some (some (34, true, true))),
 ([(10, false, false), (4, true, true), (45, true, true), (32, true, true), (37, false, false)],
  some (some (39, true, true))),
 ([(10, false, false), (4, true, true), (45, false, false), (32, false, false), (31, false, true)],
  some (some (46, true, true))),
 ([(10, false, false), (4, true, true), (45, false, false), (32, false, false), (31, true, false)],
  some (some (48, true, true))),
 ([(10, false, false), (4, true, true), (45, false, false), (32, true, true), (37, true, true)],
  some (some (46, true, true))),
 ([(10, false, false), (4, true, true), (45, false, false), (32, true, true), (37, false, false)],
  some (some (49, true, true)))]
private def goalCodes0_0_5 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(10, true, true), (50, false, true), (51, false, true), (18, false, true), (52, false, true)],
  some (some (53, false, true))),
 ([(10, true, true), (50, false, true), (51, false, true), (18, false, true), (52, true, false)],
  some (some (55, false, true))),
 ([(10, true, true), (50, false, true), (51, false, true), (18, true, false), (56, true, true)],
  some (some (53, false, true))),
 ([(10, true, true), (50, false, true), (51, false, true), (18, true, false), (56, false, false)],
  some (some (57, false, true))),
 ([(10, true, true), (50, false, true), (51, true, false), (18, false, true), (52, false, true)],
  some (some (59, false, true))),
 ([(10, true, true), (50, false, true), (51, true, false), (18, false, true), (52, true, false)],
  some (some (61, false, true))),
 ([(10, true, true), (50, false, true), (51, true, false), (18, true, false), (56, true, true)],
  some (some (59, false, true))),
 ([(10, true, true), (50, false, true), (51, true, false), (18, true, false), (56, false, false)],
  some (some (62, false, true))),
 ([(10, true, true), (50, true, false), (64, true, true), (18, false, true), (52, false, true)],
  some (some (53, false, true))),
 ([(10, true, true), (50, true, false), (64, true, true), (18, false, true), (52, true, false)],
  some (some (55, false, true))),
 ([(10, true, true), (50, true, false), (64, true, true), (18, true, false), (56, true, true)],
  some (some (53, false, true))),
 ([(10, true, true), (50, true, false), (64, true, true), (18, true, false), (56, false, false)],
  some (some (57, false, true))),
 ([(10, true, true), (50, true, false), (64, false, false), (18, false, true), (52, false, true)],
  some (some (65, false, true))),
 ([(10, true, true), (50, true, false), (64, false, false), (18, false, true), (52, true, false)],
  some (some (67, false, true))),
 ([(10, true, true), (50, true, false), (64, false, false), (18, true, false), (56, true, true)],
  some (some (65, false, true))),
 ([(10, true, true), (50, true, false), (64, false, false), (18, true, false), (56, false, false)],
  some (some (68, false, true)))]
private def goalCodes0_0_7 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(3, false, false), (6, false, false), (69, false, true), (72, false, false), (70, false, true)],
  some (some (71, true, true))),
 ([(3, false, false), (6, false, false), (69, false, true), (72, false, false), (70, true, false)],
  some (some (73, true, true))),
 ([(3, false, false), (6, false, false), (69, false, true), (72, true, true), (75, true, true)],
  some (some (71, true, true))),
 ([(3, false, false), (6, false, false), (69, false, true), (72, true, true), (75, false, false)],
  some (some (77, true, true))),
 ([(3, false, false), (6, false, false), (69, true, false), (72, false, false), (70, false, true)],
  some (some (80, true, true))),
 ([(3, false, false), (6, false, false), (69, true, false), (72, false, false), (70, true, false)],
  some (some (81, true, true))),
 ([(3, false, false), (6, false, false), (69, true, false), (72, true, true), (75, true, true)],
  some (some (80, true, true))),
 ([(3, false, false), (6, false, false), (69, true, false), (72, true, true), (75, false, false)],
  some (some (82, true, true))),
 ([(3, false, false), (6, true, true), (83, true, true), (72, false, false), (70, false, true)],
  some (some (71, true, true))),
 ([(3, false, false), (6, true, true), (83, true, true), (72, false, false), (70, true, false)],
  some (some (73, true, true))),
 ([(3, false, false), (6, true, true), (83, true, true), (72, true, true), (75, true, true)],
  some (some (71, true, true))),
 ([(3, false, false), (6, true, true), (83, true, true), (72, true, true), (75, false, false)],
  some (some (77, true, true))),
 ([(3, false, false), (6, true, true), (83, false, false), (72, false, false), (70, false, true)],
  some (some (85, true, true))),
 ([(3, false, false), (6, true, true), (83, false, false), (72, false, false), (70, true, false)],
  some (some (86, true, true))),
 ([(3, false, false), (6, true, true), (83, false, false), (72, true, true), (75, true, true)],
  some (some (85, true, true))),
 ([(3, false, false), (6, true, true), (83, false, false), (72, true, true), (75, false, false)],
  some (some (87, true, true)))]
private def goalCodes0_0_10 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(3, true, true), (89, false, true), (91, false, true), (30, false, true), (90, false, true)],
  some (some (88, false, true))),
 ([(3, true, true), (89, false, true), (91, false, true), (30, false, true), (90, true, false)],
  some (some (92, false, true))),
 ([(3, true, true), (89, false, true), (91, false, true), (30, true, false), (95, true, true)],
  some (some (88, false, true))),
 ([(3, true, true), (89, false, true), (91, false, true), (30, true, false), (95, false, false)],
  some (some (97, false, true))),
 ([(3, true, true), (89, false, true), (91, true, false), (30, false, true), (90, false, true)],
  some (some (99, false, true))),
 ([(3, true, true), (89, false, true), (91, true, false), (30, false, true), (90, true, false)],
  some (some (100, false, true))),
 ([(3, true, true), (89, false, true), (91, true, false), (30, true, false), (95, true, true)],
  some (some (99, false, true))),
 ([(3, true, true), (89, false, true), (91, true, false), (30, true, false), (95, false, false)],
  some (some (101, false, true))),
 ([(3, true, true), (89, true, false), (102, true, true), (30, false, true), (90, false, true)],
  some (some (88, false, true))),
 ([(3, true, true), (89, true, false), (102, true, true), (30, false, true), (90, true, false)],
  some (some (92, false, true))),
 ([(3, true, true), (89, true, false), (102, true, true), (30, true, false), (95, true, true)],
  some (some (88, false, true))),
 ([(3, true, true), (89, true, false), (102, true, true), (30, true, false), (95, false, false)],
  some (some (97, false, true))),
 ([(3, true, true), (89, true, false), (102, false, false), (30, false, true), (90, false, true)],
  some (some (104, false, true))),
 ([(3, true, true), (89, true, false), (102, false, false), (30, false, true), (90, true, false)],
  some (some (106, false, true))),
 ([(3, true, true), (89, true, false), (102, false, false), (30, true, false), (95, true, true)],
  some (some (104, false, true))),
 ([(3, true, true), (89, true, false), (102, false, false), (30, true, false), (95, false, false)],
  some (some (107, false, true)))]
private def goalCodes0_0_12 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(110, false, false), (109, false, false), (113, false, true), (112, false, false), (108, false, true)],
  some (some (111, true, true))),
 ([(110, false, false), (109, false, false), (113, false, true), (112, false, false), (108, true, false)],
  some (some (114, true, true))),
 ([(110, false, false), (109, false, false), (113, false, true), (112, true, true), (117, true, true)],
  some (some (111, true, true))),
 ([(110, false, false), (109, false, false), (113, false, true), (112, true, true), (117, false, false)],
  some (some (119, true, true))),
 ([(110, false, false), (109, false, false), (113, true, false), (112, false, false), (108, false, true)],
  some (some (121, true, true))),
 ([(110, false, false), (109, false, false), (113, true, false), (112, false, false), (108, true, false)],
  some (some (122, true, true))),
 ([(110, false, false), (109, false, false), (113, true, false), (112, true, true), (117, true, true)],
  some (some (121, true, true))),
 ([(110, false, false), (109, false, false), (113, true, false), (112, true, true), (117, false, false)],
  some (some (123, true, true))),
 ([(110, false, false), (109, true, true), (125, true, true), (112, false, false), (108, false, true)],
  some (some (111, true, true))),
 ([(110, false, false), (109, true, true), (125, true, true), (112, false, false), (108, true, false)],
  some (some (114, true, true))),
 ([(110, false, false), (109, true, true), (125, true, true), (112, true, true), (117, true, true)],
  some (some (111, true, true))),
 ([(110, false, false), (109, true, true), (125, true, true), (112, true, true), (117, false, false)],
  some (some (119, true, true))),
 ([(110, false, false), (109, true, true), (125, false, false), (112, false, false), (108, false, true)],
  some (some (126, true, true))),
 ([(110, false, false), (109, true, true), (125, false, false), (112, false, false), (108, true, false)],
  some (some (128, true, true))),
 ([(110, false, false), (109, true, true), (125, false, false), (112, true, true), (117, true, true)],
  some (some (126, true, true))),
 ([(110, false, false), (109, true, true), (125, false, false), (112, true, true), (117, false, false)],
  some (some (129, true, true)))]
private def goalCodes0_0_15 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(110, true, true), (132, false, true), (133, false, true)], some (some (130, false, true))),
 ([(110, true, true), (132, false, true), (133, true, false)], some (some (135, false, true))),
 ([(110, true, true), (132, true, false), (136, true, true)], some (some (130, false, true))),
 ([(110, true, true), (132, true, false), (136, false, false)], some (some (139, false, true)))]
private def goalCodes0_0_17 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(3, false, false), (10, false, false), (4, false, false), (9, false, true)], some (some (1, true, false))),
 ([(3, false, false), (10, false, false), (4, false, false), (9, true, false)], some (some (23, true, false))),
 ([(3, false, false), (10, false, false), (4, true, true), (26, true, true)], some (some (1, true, false))),
 ([(3, false, false), (10, false, false), (4, true, true), (26, false, false)], some (some (27, true, false))),
 ([(3, false, false), (10, true, true)], some (some (1, true, false))),
 ([(3, true, true), (30, false, false), (29, false, true), (10, false, false), (4, false, false), (9, false, true)],
  some (some (1, true, false))),
 ([(3, true, true), (30, false, false), (29, false, true), (10, false, false), (4, false, false), (9, true, false)],
  some (some (23, true, false))),
 ([(3, true, true), (30, false, false), (29, false, true), (10, false, false), (4, true, true), (26, true, true)],
  some (some (1, true, false))),
 ([(3, true, true), (30, false, false), (29, false, true), (10, false, false), (4, true, true), (26, false, false)],
  some (some (27, true, false))),
 ([(3, true, true), (30, false, false), (29, false, true), (10, true, true)], some (some (1, true, false))),
 ([(3, true, true), (30, false, false), (29, true, false), (10, false, false), (4, false, false), (9, false, true)],
  some (some (143, true, false))),
 ([(3, true, true), (30, false, false), (29, true, false), (10, false, false), (4, false, false), (9, true, false)],
  some (some (145, true, false))),
 ([(3, true, true), (30, false, false), (29, true, false), (10, false, false), (4, true, true), (26, true, true)],
  some (some (143, true, false))),
 ([(3, true, true), (30, false, false), (29, true, false), (10, false, false), (4, true, true), (26, false, false)],
  some (some (146, true, false))),
 ([(3, true, true), (30, false, false), (29, true, false), (10, true, true)], some (some (143, true, false))),
 ([(3, true, true), (30, true, true), (147, true, true), (10, false, false), (4, false, false), (9, false, true)],
  some (some (1, true, false))),
 ([(3, true, true), (30, true, true), (147, true, true), (10, false, false), (4, false, false), (9, true, false)],
  some (some (23, true, false))),
 ([(3, true, true), (30, true, true), (147, true, true), (10, false, false), (4, true, true), (26, true, true)],
  some (some (1, true, false))),
 ([(3, true, true), (30, true, true), (147, true, true), (10, false, false), (4, true, true), (26, false, false)],
  some (some (27, true, false))),
 ([(3, true, true), (30, true, true), (147, true, true), (10, true, true)], some (some (1, true, false))),
 ([(3, true, true), (30, true, true), (147, false, false), (10, false, false), (4, false, false), (9, false, true)],
  some (some (148, true, false))),
 ([(3, true, true), (30, true, true), (147, false, false), (10, false, false), (4, false, false), (9, true, false)],
  some (some (150, true, false))),
 ([(3, true, true), (30, true, true), (147, false, false), (10, false, false), (4, true, true), (26, true, true)],
  some (some (148, true, false))),
 ([(3, true, true), (30, true, true), (147, false, false), (10, false, false), (4, true, true), (26, false, false)],
  some (some (151, true, false))),
 ([(3, true, true), (30, true, true), (147, false, false), (10, true, true)], some (some (148, true, false)))]
private def goalCodes0_0_19 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(110, false, false), (3, false, false), (6, false, false), (2, false, true)], some (some (152, true, false))),
 ([(110, false, false), (3, false, false), (6, false, false), (2, true, false)], some (some (153, true, false))),
 ([(110, false, false), (3, false, false), (6, true, true), (13, true, true)], some (some (152, true, false))),
 ([(110, false, false), (3, false, false), (6, true, true), (13, false, false)], some (some (154, true, false))),
 ([(110, false, false), (3, true, true)], some (some (152, true, false))),
 ([(110, true, true), (156, false, false), (155, false, true), (3, false, false), (6, false, false), (2, false, true)],
  some (some (152, true, false))),
 ([(110, true, true), (156, false, false), (155, false, true), (3, false, false), (6, false, false), (2, true, false)],
  some (some (153, true, false))),
 ([(110, true, true), (156, false, false), (155, false, true), (3, false, false), (6, true, true), (13, true, true)],
  some (some (152, true, false))),
 ([(110, true, true), (156, false, false), (155, false, true), (3, false, false), (6, true, true), (13, false, false)],
  some (some (154, true, false))),
 ([(110, true, true), (156, false, false), (155, false, true), (3, true, true)], some (some (152, true, false))),
 ([(110, true, true), (156, false, false), (155, true, false), (3, false, false), (6, false, false), (2, false, true)],
  some (some (157, true, false))),
 ([(110, true, true), (156, false, false), (155, true, false), (3, false, false), (6, false, false), (2, true, false)],
  some (some (159, true, false))),
 ([(110, true, true), (156, false, false), (155, true, false), (3, false, false), (6, true, true), (13, true, true)],
  some (some (157, true, false))),
 ([(110, true, true), (156, false, false), (155, true, false), (3, false, false), (6, true, true), (13, false, false)],
  some (some (160, true, false))),
 ([(110, true, true), (156, false, false), (155, true, false), (3, true, true)], some (some (157, true, false))),
 ([(110, true, true), (156, true, true), (162, true, true), (3, false, false), (6, false, false), (2, false, true)],
  some (some (152, true, false))),
 ([(110, true, true), (156, true, true), (162, true, true), (3, false, false), (6, false, false), (2, true, false)],
  some (some (153, true, false))),
 ([(110, true, true), (156, true, true), (162, true, true), (3, false, false), (6, true, true), (13, true, true)],
  some (some (152, true, false))),
 ([(110, true, true), (156, true, true), (162, true, true), (3, false, false), (6, true, true), (13, false, false)],
  some (some (154, true, false))),
 ([(110, true, true), (156, true, true), (162, true, true), (3, true, true)], some (some (152, true, false))),
 ([(110, true, true), (156, true, true), (162, false, false), (3, false, false), (6, false, false), (2, false, true)],
  some (some (164, true, false))),
 ([(110, true, true), (156, true, true), (162, false, false), (3, false, false), (6, false, false), (2, true, false)],
  some (some (165, true, false))),
 ([(110, true, true), (156, true, true), (162, false, false), (3, false, false), (6, true, true), (13, true, true)],
  some (some (164, true, false))),
 ([(110, true, true), (156, true, true), (162, false, false), (3, false, false), (6, true, true), (13, false, false)],
  some (some (166, true, false))),
 ([(110, true, true), (156, true, true), (162, false, false), (3, true, true)], some (some (164, true, false)))]
private def goalCodes0_0_20 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([(10, false, false), (8, false, false), (17, false, true)], some none),
 ([(10, false, false), (8, false, false), (17, true, false)], some none),
 ([(10, false, false), (8, true, true), (20, true, true)], some none),
 ([(10, false, false), (8, true, true), (20, false, false)], some none),
 ([(10, true, true), (18, false, false), (17, false, true), (8, false, false), (17, false, true)], some none),
 ([(10, true, true), (18, false, false), (17, false, true), (8, false, false), (17, true, false)], some none),
 ([(10, true, true), (18, false, false), (17, false, true), (8, true, true), (20, true, true)], some none),
 ([(10, true, true), (18, false, false), (17, false, true), (8, true, true), (20, false, false)], some none),
 ([(10, true, true), (18, false, false), (17, true, false), (8, false, false), (17, false, true)], none),
 ([(10, true, true), (18, false, false), (17, true, false), (8, false, false), (17, true, false)], some none),
 ([(10, true, true), (18, false, false), (17, true, false), (8, true, true), (20, true, true)], none),
 ([(10, true, true), (18, false, false), (17, true, false), (8, true, true), (20, false, false)],
  some (some (168, false, false))),
 ([(10, true, true), (18, true, true), (20, true, true), (8, false, false), (17, false, true)], some none),
 ([(10, true, true), (18, true, true), (20, true, true), (8, false, false), (17, true, false)], some none),
 ([(10, true, true), (18, true, true), (20, true, true), (8, true, true), (20, true, true)], some none),
 ([(10, true, true), (18, true, true), (20, true, true), (8, true, true), (20, false, false)], some none),
 ([(10, true, true), (18, true, true), (20, false, false), (8, false, false), (17, false, true)], none),
 ([(10, true, true), (18, true, true), (20, false, false), (8, false, false), (17, true, false)],
  some (some (168, true, false))),
 ([(10, true, true), (18, true, true), (20, false, false), (8, true, true), (20, true, true)], none),
 ([(10, true, true), (18, true, true), (20, false, false), (8, true, true), (20, false, false)], some none)]
private def goalCodes0_1_0 : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) := [([], none)]
private def cutCodes0_0 : List (ℕ × Bool × Bool) := [(7, false, true)]
private def cutCodes0_1 : List (ℕ × Bool × Bool) := [(7, true, false), (177, false, false), (176, true, false)]

private theorem hGoal0_0_0 : trunkGoalBranches (trunkCatalog.states 0) 0 0 = goalCodes0_0_0.map decodeGoalBranch := by decide +kernel

private theorem hGoal0_0_2 : trunkGoalBranches (trunkCatalog.states 0) 0 2 = goalCodes0_0_2.map decodeGoalBranch := by decide +kernel

private theorem hGoal0_0_5 : trunkGoalBranches (trunkCatalog.states 0) 0 5 = goalCodes0_0_5.map decodeGoalBranch := by decide +kernel

private theorem hGoal0_0_7 : trunkGoalBranches (trunkCatalog.states 0) 0 7 = goalCodes0_0_7.map decodeGoalBranch := by decide +kernel

private theorem hGoal0_0_10 : trunkGoalBranches (trunkCatalog.states 0) 0 10 = goalCodes0_0_10.map decodeGoalBranch := by decide +kernel

private theorem hGoal0_0_12 : trunkGoalBranches (trunkCatalog.states 0) 0 12 = goalCodes0_0_12.map decodeGoalBranch := by decide +kernel

private theorem hGoal0_0_15 : trunkGoalBranches (trunkCatalog.states 0) 0 15 = goalCodes0_0_15.map decodeGoalBranch := by decide +kernel

private theorem hGoal0_0_17 : trunkGoalBranches (trunkCatalog.states 0) 0 17 = goalCodes0_0_17.map decodeGoalBranch := by decide +kernel

private theorem hGoal0_0_19 : trunkGoalBranches (trunkCatalog.states 0) 0 19 = goalCodes0_0_19.map decodeGoalBranch := by decide +kernel

private theorem hGoal0_0_20 : trunkGoalBranches (trunkCatalog.states 0) 0 20 = goalCodes0_0_20.map decodeGoalBranch := by decide +kernel

private theorem hGoal0_1_0 : trunkGoalBranches (trunkCatalog.states 0) 1 0 = goalCodes0_1_0.map decodeGoalBranch := by decide +kernel

private theorem hCut0_0 : (trunkPlanAt (trunkCatalog.states 0) 0).cuts = cutCodes0_0.map decodeThresholdBound := by decide +kernel

private theorem hCut0_1 : (trunkPlanAt (trunkCatalog.states 0) 1).cuts = cutCodes0_1.map decodeThresholdBound := by decide +kernel

private def codedGoals0 (pi goal : ℕ) : List (List (ℕ × Bool × Bool) × Option (Option (ℕ × Bool × Bool))) :=
  if pi = 0 ∧ goal = 0 then goalCodes0_0_0 else
  if pi = 0 ∧ goal = 2 then goalCodes0_0_2 else
  if pi = 0 ∧ goal = 5 then goalCodes0_0_5 else
  if pi = 0 ∧ goal = 7 then goalCodes0_0_7 else
  if pi = 0 ∧ goal = 10 then goalCodes0_0_10 else
  if pi = 0 ∧ goal = 12 then goalCodes0_0_12 else
  if pi = 0 ∧ goal = 15 then goalCodes0_0_15 else
  if pi = 0 ∧ goal = 17 then goalCodes0_0_17 else
  if pi = 0 ∧ goal = 19 then goalCodes0_0_19 else
  if pi = 0 ∧ goal = 20 then goalCodes0_0_20 else
  if pi = 1 ∧ goal = 0 then goalCodes0_1_0 else
  []

private def codedKeys0 : List (ℕ × ℕ) := [(0, 0), (0, 2), (0, 5), (0, 7), (0, 10), (0, 12), (0, 15), (0, 17), (0, 19), (0, 20), (1, 0)]

private theorem hCodedGoals0 (pi goal : ℕ) (hm : (pi,goal) ∈ codedKeys0) : trunkGoalBranches (trunkCatalog.states 0) pi goal = (codedGoals0 pi goal).map decodeGoalBranch := by
  unfold codedGoals0
  by_cases h0 : pi = 0 ∧ goal = 0
  · rw [if_pos h0]
    rcases h0 with ⟨rfl,rfl⟩
    exact hGoal0_0_0
  rw [if_neg h0]
  by_cases h1 : pi = 0 ∧ goal = 2
  · rw [if_pos h1]
    rcases h1 with ⟨rfl,rfl⟩
    exact hGoal0_0_2
  rw [if_neg h1]
  by_cases h2 : pi = 0 ∧ goal = 5
  · rw [if_pos h2]
    rcases h2 with ⟨rfl,rfl⟩
    exact hGoal0_0_5
  rw [if_neg h2]
  by_cases h3 : pi = 0 ∧ goal = 7
  · rw [if_pos h3]
    rcases h3 with ⟨rfl,rfl⟩
    exact hGoal0_0_7
  rw [if_neg h3]
  by_cases h4 : pi = 0 ∧ goal = 10
  · rw [if_pos h4]
    rcases h4 with ⟨rfl,rfl⟩
    exact hGoal0_0_10
  rw [if_neg h4]
  by_cases h5 : pi = 0 ∧ goal = 12
  · rw [if_pos h5]
    rcases h5 with ⟨rfl,rfl⟩
    exact hGoal0_0_12
  rw [if_neg h5]
  by_cases h6 : pi = 0 ∧ goal = 15
  · rw [if_pos h6]
    rcases h6 with ⟨rfl,rfl⟩
    exact hGoal0_0_15
  rw [if_neg h6]
  by_cases h7 : pi = 0 ∧ goal = 17
  · rw [if_pos h7]
    rcases h7 with ⟨rfl,rfl⟩
    exact hGoal0_0_17
  rw [if_neg h7]
  by_cases h8 : pi = 0 ∧ goal = 19
  · rw [if_pos h8]
    rcases h8 with ⟨rfl,rfl⟩
    exact hGoal0_0_19
  rw [if_neg h8]
  by_cases h9 : pi = 0 ∧ goal = 20
  · rw [if_pos h9]
    rcases h9 with ⟨rfl,rfl⟩
    exact hGoal0_0_20
  rw [if_neg h9]
  by_cases h10 : pi = 1 ∧ goal = 0
  · rw [if_pos h10]
    rcases h10 with ⟨rfl,rfl⟩
    exact hGoal0_1_0
  rw [if_neg h10]
  simp_all only [codedKeys0,List.mem_cons,List.mem_nil_iff,or_false,Prod.mk.injEq]

private def codedCuts0 (pi : ℕ) : List (ℕ × Bool × Bool) :=
  if pi = 0 then cutCodes0_0 else
  if pi = 1 then cutCodes0_1 else
  []

private theorem hCodedCuts0 (pi goal : ℕ) (hm : (pi,goal) ∈ codedKeys0) : (trunkPlanAt (trunkCatalog.states 0) pi).cuts = (codedCuts0 pi).map decodeThresholdBound := by
  unfold codedCuts0
  by_cases h0 : pi = 0
  · rw [if_pos h0]
    subst pi
    exact hCut0_0
  rw [if_neg h0]
  by_cases h1 : pi = 1
  · rw [if_pos h1]
    subst pi
    exact hCut0_1
  rw [if_neg h1]
  simp_all only [codedKeys0,List.mem_cons,List.mem_nil_iff,or_false,Prod.mk.injEq,false_and]

private def codedValid0 (g : TrunkGroup) : Prop := (g.plan,g.goal) ∈ codedKeys0 ∧ codeGroupValid (trunkCatalog.states 0) codedParents0 codedCuts0 codedGoals0 g

private theorem codedValid0_sound (g : TrunkGroup) (h : codedValid0 g) : trunkGroupValidFast 0 g :=
  codeGroupValid_sound 0 codedParents0 codedCuts0 codedGoals0 g hCodedParents0 (hCodedCuts0 g.plan g.goal h.1) (hCodedGoals0 g.plan g.goal h.1) h.2



set_option Elab.async false
theorem batch_chunk_0 : ∀ j ∈ List.range 20, codedValid0 (trunkStateData00Part01.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid0 codeGroupValid
  decide +kernel

theorem batch_chunk_20 : ∀ j ∈ List.range' 20 20, codedValid0 (trunkStateData00Part01.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid0 codeGroupValid
  decide +kernel

theorem batch_chunk_40 : ∀ j ∈ List.range' 40 20, codedValid0 (trunkStateData00Part01.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid0 codeGroupValid
  decide +kernel

theorem batch_chunk_60 : ∀ j ∈ List.range' 60 20, codedValid0 (trunkStateData00Part01.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid0 codeGroupValid
  decide +kernel

theorem batch_chunk_80 : ∀ j ∈ List.range' 80 20, codedValid0 (trunkStateData00Part01.getD j ⟨0,[],0,[]⟩) := by
  unfold codedValid0 codeGroupValid
  decide +kernel

theorem batch_key (j : ℕ) (hj : j < 100) : codedValid0 (trunkStateData00Part01.getD j ⟨0,[],0,[]⟩) := by
  rcases lt_or_ge j 20 with h0 | h0
  · exact batch_chunk_0 j (List.mem_range.2 (by omega))
  rcases lt_or_ge j 40 with h1 | h1
  · exact batch_chunk_20 j (List.mem_range'.2 ⟨j - 20, by omega, by omega⟩)
  rcases lt_or_ge j 60 with h2 | h2
  · exact batch_chunk_40 j (List.mem_range'.2 ⟨j - 40, by omega, by omega⟩)
  rcases lt_or_ge j 80 with h3 | h3
  · exact batch_chunk_60 j (List.mem_range'.2 ⟨j - 60, by omega, by omega⟩)
  · exact batch_chunk_80 j (List.mem_range'.2 ⟨j - 80, by omega, by omega⟩)

theorem part_length_1 : trunkStateData00Part01.length = 100 := by decide +kernel

theorem part_length_2 : trunkStateData00Part02.length = 100 := by decide +kernel

theorem part_length_3 : trunkStateData00Part03.length = 100 := by decide +kernel

theorem part_length_4 : trunkStateData00Part04.length = 100 := by decide +kernel

theorem solution : trunkBindingBatch 0 0 100 := by
  intro i hlo hhi g hg
  change (trunkStateData00Part01 ++ trunkStateData00Part02 ++ trunkStateData00Part03 ++ trunkStateData00Part04 ++ trunkStateData00Part05)[i]? = some g at hg
  rw [List.getElem?_append_left (show i < (trunkStateData00Part01 ++ trunkStateData00Part02 ++ trunkStateData00Part03 ++ trunkStateData00Part04).length by simp only [List.length_append, part_length_1, part_length_2, part_length_3, part_length_4, Nat.reduceAdd]; omega)] at hg
  rw [List.getElem?_append_left (show i < (trunkStateData00Part01 ++ trunkStateData00Part02 ++ trunkStateData00Part03).length by simp only [List.length_append, part_length_1, part_length_2, part_length_3, part_length_4, Nat.reduceAdd]; omega)] at hg
  rw [List.getElem?_append_left (show i < (trunkStateData00Part01 ++ trunkStateData00Part02).length by simp only [List.length_append, part_length_1, part_length_2, part_length_3, part_length_4, Nat.reduceAdd]; omega)] at hg
  rw [List.getElem?_append_left (show i < (trunkStateData00Part01).length by simp only [List.length_append, part_length_1, part_length_2, part_length_3, part_length_4, Nat.reduceAdd]; omega)] at hg
  have hgi := batch_key (i - 0) (by omega)
  have hgv : trunkStateData00Part01.getD (i - 0) ⟨0,[],0,[]⟩ = g := by
    try simp only [Nat.sub_zero]
    rw [List.getD_eq_getElem?_getD, hg]; rfl
  rw [hgv] at hgi
  exact Freiman.trunkFast_correctness.2 0 hPar0 g (codedValid0_sound g hgi)

#print axioms solution
